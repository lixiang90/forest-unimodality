import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell028.Parameters
import ForestUnimodality.BinomialMassData.Q17_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q17_37.Batch050_099
import ForestUnimodality.BinomialMassData.Q17_37.Batch100_149
import ForestUnimodality.BinomialMassData.Q17_37.Batch150_199
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch000_049
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch050_099
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch100_149
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree000.table
  base := (2388757946927717709161953477/50000000000000000000000000)
  polynomial :=
    { denominator := 46250000000000000000000000000000000000000
      center := (260)
      previous := (221)
      next := (0)
      square := (3530649028151703668759742170000000000000)
      linear := (17613393416737128313598326362500000000000)
      constant := (2209601100908138880974806966225000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree000.table
  base := (2388757946927717709161953477/50000000000000000000000000)
  polynomial :=
    { denominator := 4347500000000000000000000000000000000000000
      center := (24245)
      previous := (20969)
      next := (0)
      square := (331881008646260144863415763980000000000000)
      linear := (1655658981173290061478242678075000000000000)
      constant := (207702503485365054811631854825150000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree001.table
  base := (73419823285674846032067152785825895276677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (1063306978924231645730613683265000000000000)
      constant := (99968037165116333874711727742450650633770813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree001.table
  base := (58392232691700817067056514113801601787759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (9375467605255735212983897559490740000000000000)
      constant := (878081266655290622547867757962297698999997674195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49835375444826417891/100000000000000000000)
  directionHi := (12458843861206604473/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree002.table
  base := (11759065491361865646884857442693649387603/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (411611422504957898127475607852500000000000)
      constant := (31707774865572789817456673931730212023257014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree002.table
  base := (11636869824094109569079344275004486621381/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (1808542834367516189581284762572945000000000000)
      constant := (138591168629865517265427283563396977343749324404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49835375444826417891/100000000000000000000)
  centralHi := (12458843861206604473/25000000000000000000)
  directionLo := (550608311250223709/781250000000000000)
  directionHi := (70477863840028634753/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree003.table
  base := (126448108852288267607348774850778131439619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (2332554844382399787117154992580000000000000)
      constant := (167906757179829042703581347914095261940838411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree003.table
  base := (62374976159730092053931201162745340011809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (2546437534842197151833190270546410000000000000)
      constant := (182852157650915279675627539797496285381851844889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/781250000000000000)
  centralHi := (70477863840028634753/100000000000000000000)
  directionLo := (86317402284709794589/100000000000000000000)
  directionHi := (8631740228470979459/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree004.table
  base := (44683298906900469380481012284091475948001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (686109154362568194607252561170000000000000)
      constant := (58145536016483268303752198645681230572813369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree004.table
  base := (22005746289350749362401112971307959979443/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (737894700474680962251905507973465000000000000)
      constant := (63193031318075936726151030280629169240993144603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86317402284709794589/100000000000000000000)
  centralHi := (8631740228470979459/10000000000000000000)
  directionLo := (99670750889652835783/100000000000000000000)
  directionHi := (12458843861206604473/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree005.table
  base := (66236143837706901479704313134428132973557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (411881773067872991311855252100000000000000)
      constant := (84215619710092702819882210252532114040799533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree005.table
  base := (13041282912331280912000194853325189255607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (810282534113053394348863522694900000000000000)
      constant := (182899731475806340072163308154027873284277482235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99670750889652835783/100000000000000000000)
  centralHi := (12458843861206604473/12500000000000000000)
  directionLo := (22287057435771138107/20000000000000000000)
  directionHi := (13929410897356961317/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree006.table
  base := (3195633699818466320078529838758668834063/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-68556845323673800823849327267500000000000)
      constant := (7945859279133350046922481559186235267664494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree006.table
  base := (12585246194882214493782013351477350907103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-332753433418154265077473746626015000000000000)
      constant := (34516405861563255911445895929715332902539231463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22287057435771138107/20000000000000000000)
  centralHi := (13929410897356961317/12500000000000000000)
  directionLo := (23842039253877143/19531250000000000)
  directionHi := (122071240979850972161/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree007.table
  base := (8146902933754502044127203770005177091457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-1508791298246653804493444488380000000000000)
      constant := (49807874835336096154436283404665437191023165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree007.table
  base := (2507386811978598056696691454080087464651/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-868077500364571878742163373925755000000000000)
      constant := (27066119058141395358399403551239205234751387084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23842039253877143/19531250000000000)
  centralHi := (122071240979850972161/100000000000000000000)
  directionLo := (8240750620034099977/6250000000000000000)
  directionHi := (131852009920545599633/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree008.table
  base := (16591288629410769324276408483234090247211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-1234563916951958601198047179310000000000000)
      constant := (20191559404114443895026664069787469548431859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree008.table
  base := (16343546066788113472872350103267407799173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-2806803134621978984813706002450990000000000000)
      constant := (43949419118327545165629160750317896541042851933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8240750620034099977/6250000000000000000)
  centralHi := (131852009920545599633/100000000000000000000)
  directionLo := (550608311250223709/390625000000000000)
  directionHi := (28191145536011453901/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree009.table
  base := (27411463856778173268971850668990035558481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-3429464369561180600298744228860000000000000)
      constant := (33837546553519448458999042791667358679560489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree009.table
  base := (6750078056356741856126466646974219377151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-1938725634257407106071542628525235000000000000)
      constant := (18450324904552951196475453527590680777049259271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/390625000000000000)
  centralHi := (28191145536011453901/20000000000000000000)
  directionLo := (5980245053379170147/4000000000000000000)
  directionHi := (37376531583619813419/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree010.table
  base := (5701608751893482268704485065225509935859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-1097450226304610999550348524775000000000000)
      constant := (7332394939304755546646876589043723102190971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree010.table
  base := (22455248402909080844266830236883299633649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-9896198804815298878944929023299900000000000000)
      constant := (64149522448885798886207567132952260971410247529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5980245053379170147/4000000000000000000)
  centralHi := (37376531583619813419/25000000000000000000)
  directionLo := (2462395225863724861/1562500000000000000)
  directionHi := (31518658891055678221/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree011.table
  base := (3800800792744023450222559743843490698047/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-5350137440875707396104043969340000000000000)
      constant := (26361605062015593985113443898628693828131715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree011.table
  base := (18696992835109084794031002319367886940621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-12037495072600969333603687532498860000000000000)
      constant := (57870222504147161289950165346757863622757719141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2462395225863724861/1562500000000000000)
  centralHi := (31518658891055678221/20000000000000000000)
  directionLo := (8264262081849002987/5000000000000000000)
  directionHi := (165285241636980059741/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree012.table
  base := (15782756315310218555784645842118526161739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-6310473976532970794006693839580000000000000)
      constant := (24630506140747139012180588322740262315420691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree012.table
  base := (15509830542293012411185608565359221223423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-14178791340386639788262446041697820000000000000)
      constant := (54311051583767828394598203213638813445399186183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8264262081849002987/5000000000000000000)
  centralHi := (165285241636980059741/100000000000000000000)
  directionLo := (172634804569419589179/100000000000000000000)
  directionHi := (8631740228470979459/5000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree013.table
  base := (13002619533984434752108951281404592982059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-7270810512190234191909343709820000000000000)
      constant := (23944523702089093481713057581822887792438771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree013.table
  base := (1275731696435595698338221507858048076109/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-8160043804086155121460602275448390000000000000)
      constant := (26529692414099394804148911235376276029854125945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172634804569419589179/100000000000000000000)
  centralHi := (8631740228470979459/5000000000000000000)
  directionLo := (701890630852815093/390625000000000000)
  directionHi := (179684001498320663809/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree014.table
  base := (2114186263683851739668764115292710479223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-8231147047847497589811993580060000000000000)
      constant := (24176803055529576116666198159298603230281435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree014.table
  base := (10349025032467219030800695696481200197121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-18461383875957980697579963060095740000000000000)
      constant := (53841759839620681189435903367280803621317755641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (701890630852815093/390625000000000000)
  centralHi := (179684001498320663809/100000000000000000000)
  directionLo := (46616725163946865379/25000000000000000000)
  directionHi := (186466900655787461517/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree015.table
  base := (131614919168848108256449944123957721723/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-1148935447938095123464330431287500000000000)
      constant := (3154908383079108952497667500858084968310296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree015.table
  base := (4110979616866311618911500135119328154709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-10301340071871825576119360784647350000000000000)
      constant := (28233835282292228394185136234557822778546735789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46616725163946865379/25000000000000000000)
  centralHi := (186466900655787461517/100000000000000000000)
  directionLo := (96505789574903378351/50000000000000000000)
  directionHi := (193011579149806756703/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree016.table
  base := (6513038673137092713941506129745209788679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-10151820119162024385617293320540000000000000)
      constant := (27067776181953476656513966906341192200701551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree016.table
  base := (1582514095589714155862757714721758449501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-5685994102882330401724370019623415000000000000)
      constant := (15199454088901414239922995208231398884063413621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96505789574903378351/50000000000000000000)
  centralHi := (193011579149806756703/100000000000000000000)
  directionLo := (199341501779305671567/100000000000000000000)
  directionHi := (12458843861206604473/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree017.table
  base := (600546424854729675277074391684824828059/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-1389019581852410972939992898847500000000000)
      constant := (3701697290087971656837437058064025189612771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree017.table
  base := (4638161957432240113074889375952382934767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-24885272679314992061556238587692620000000000000)
      constant := (66725885687744285626612668847544966233070514807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199341501779305671567/100000000000000000000)
  centralHi := (12458843861206604473/6250000000000000000)
  directionLo := (51369129212833006539/25000000000000000000)
  directionHi := (205476516851332026157/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree018.table
  base := (326930958014565865602143682277832310767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-6036246595238275590711296530510000000000000)
      constant := (16419141016876206913444183424531762167200115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree018.table
  base := (3118497508677491727665591211582213326081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-27026568947100662516214997096891580000000000000)
      constant := (74167873166175406775429224545642034545881399801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51369129212833006539/25000000000000000000)
  centralHi := (205476516851332026157/100000000000000000000)
  directionLo := (1651824933750671127/781250000000000000)
  directionHi := (211433591520085904257/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree019.table
  base := (117822420156254915209086271045245130069/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-1629103715766726822415655366407500000000000)
      constant := (4588852319755763027632249628924381166128922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree019.table
  base := (437131582627113074824363103216971126299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-7291966303721583242718438901522635000000000000)
      constant := (20763906266566274789268765161465692439434458179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1651824933750671127/781250000000000000)
  centralHi := (211433591520085904257/100000000000000000000)
  directionLo := (54306841344351674309/25000000000000000000)
  directionHi := (217227365377406697237/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree020.table
  base := (316591781439100710866328052872900977467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-6996583130895538988613946400750000000000000)
      constant := (20602769659253249945993219235383001438152323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree020.table
  base := (101922764489229527589481697730729276233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-31309161482672003425532514115289500000000000000)
      constant := (93332788101378286865043437336148753747855080965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54306841344351674309/25000000000000000000)
  centralHi := (217227365377406697237/100000000000000000000)
  directionLo := (222870574357711381071/100000000000000000000)
  directionHi := (13929410897356961317/6250000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree021.table
  base := (-251150166799522403233012331288832429837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-7476751398724170687565271335870000000000000)
      constant := (23150486161892075774345907405175588403553147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree021.table
  base := (-613852336266950285208347482275976553697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-33450457750457673880191272624488460000000000000)
      constant := (104952148724453393479279674806106921508457274663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222870574357711381071/100000000000000000000)
  centralHi := (13929410897356961317/6250000000000000000)
  directionLo := (114187190131230313137/50000000000000000000)
  directionHi := (9134975210498425051/4000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree022.table
  base := (-767274628025060142009995747682348091047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-7956919666552802386516596270990000000000000)
      constant := (25989484857037943559411456963762865463356657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree022.table
  base := (-817534617586396362765075065285359438179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-17795877009121672167425015566843710000000000000)
      constant := (58936898669933861913736111266081083530454684341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/50000000000000000000)
  centralHi := (9134975210498425051/4000000000000000000)
  directionLo := (233748630383131386503/100000000000000000000)
  directionHi := (29218578797891423313/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree023.table
  base := (-154677447981132405641088099880673410997/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-2109271983595358521366980301527500000000000)
      constant := (7278011836966161453647434706999216200690214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree023.table
  base := (-2565258512508170741741422858909257135107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-37733050286029014789508789642886380000000000000)
      constant := (132063798355774995096323342610382448403323084053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233748630383131386503/100000000000000000000)
  centralHi := (29218578797891423313/12500000000000000000)
  directionLo := (239002064534423177953/100000000000000000000)
  directionHi := (119501032267211588977/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree024.table
  base := (-666560464851211464179417358283935813833/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-17834512404420131568838492282460000000000000)
      constant := (65023160710673243580522458089266459354313115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree024.table
  base := (-170699962617393454476988344667351423477/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-9968586638453671311041887038021335000000000000)
      constant := (36873295865715971283912012380856942729416556415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239002064534423177953/100000000000000000000)
  centralHi := (119501032267211588977/50000000000000000000)
  directionLo := (244142481959701944321/100000000000000000000)
  directionHi := (122071240979850972161/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree025.table
  base := (-2058344965977058283000211969396616006951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-9397424470038697483370571076350000000000000)
      constant := (36182435928789313420128898722646032686484081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree025.table
  base := (-1047372319713342728903587279459646924669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-10503910705400088924706576665321075000000000000)
      constant := (41034290362233336342599388306256650582523059051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244142481959701944321/100000000000000000000)
  centralHi := (122071240979850972161/50000000000000000000)
  directionLo := (249176877224132089459/100000000000000000000)
  directionHi := (12458843861206604473/5000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree026.table
  base := (-2416791596581352302514089038015184520161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-9877592737867329182321896011470000000000000)
      constant := (40119766985200176168451859671017212391899591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree026.table
  base := (-2449378023978068036485092933563621743021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-22078469544693013076742532585241630000000000000)
      constant := (90987240218462236749221235355969336650873590459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249176877224132089459/100000000000000000000)
  centralHi := (12458843861206604473/5000000000000000000)
  directionLo := (254111551860392614291/100000000000000000000)
  directionHi := (63527887965098153573/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree027.table
  base := (-686195825652354995551124881032844251521/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-2589440251423990220318305236647500000000000)
      constant := (11079852171535505213472425267688536219667751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree027.table
  base := (-1109566069717769001106114653102856897861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-46298235357171696608143823679682220000000000000)
      constant := (200986902591379383003025039785445846475918474095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254111551860392614291/100000000000000000000)
  centralHi := (63527887965098153573/25000000000000000000)
  directionLo := (32369025856766172971/12500000000000000000)
  directionHi := (258952206854129383769/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree028.table
  base := (-6089872474494117126172467062047952248479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-21675858547049185160449091763420000000000000)
      constant := (97555559035806982106986350540936353371832249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree028.table
  base := (-6141891416605256071704680630290109624623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-48439531624957367062802582188881180000000000000)
      constant := (221158765276388770303554564920574563391875468617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32369025856766172971/12500000000000000000)
  centralHi := (258952206854129383769/100000000000000000000)
  directionLo := (52740803968218239853/20000000000000000000)
  directionHi := (131852009920545599633/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree029.table
  base := (-6639002713019303785603015004055307631379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-22636195082706448558351741633660000000000000)
      constant := (106983595843399052559680175918468283852642149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree029.table
  base := (-668538934203283984611339568006266255243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-25290413946371518758730670349040070000000000000)
      constant := (121238305440624335529218976264420225429641417985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52740803968218239853/20000000000000000000)
  centralHi := (131852009920545599633/50000000000000000000)
  directionLo := (268371709995814254751/100000000000000000000)
  directionHi := (8386615937369195461/3125000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree030.table
  base := (-17852080567680006317648232735465526257/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-2949566452295463994531798937987500000000000)
      constant := (14614702881045776890984235765382384727708350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree030.table
  base := (-224442155961622295723524434403003271737/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-13180531040132176993030024801819775000000000000)
      constant := (66232218137166938078722061176175917742971454584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268371709995814254751/100000000000000000000)
  centralHi := (8386615937369195461/3125000000000000000)
  directionLo := (5459191858574096191/2000000000000000000)
  directionHi := (272959592928704809551/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree031.table
  base := (-1519739420047740627912935024474154343901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-24556868154020975354157041374140000000000000)
      constant := (127353073552278565290394482436294413515997655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree031.table
  base := (-3817729304729213008597854906052351703061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-27431710214157189213389428858239030000000000000)
      constant := (144252803111470530530840730940212521115387465619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5459191858574096191/2000000000000000000)
  centralHi := (272959592928704809551/100000000000000000000)
  directionLo := (27747162740995888093/10000000000000000000)
  directionHi := (277471627409958880931/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree032.table
  base := (-1001933755721216613719451023987328530269/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-3189650586209779844007461405547500000000000)
      constant := (17285751826337050623979583596721347242061739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree032.table
  base := (-80481455833682447400711310529470962799/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-14251179174025012220359404056419255000000000000)
      constant := (78299565387220189102457950748934523562733133025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27747162740995888093/10000000000000000000)
  centralHi := (277471627409958880931/100000000000000000000)
  directionLo := (550608311250223709/195312500000000000)
  directionHi := (281911455360114539009/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree033.table
  base := (-1678725020299129400265529023096442074247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-26477541225335502149962341114620000000000000)
      constant := (149713059265829704213101233334884854001779285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree033.table
  base := (-4211320664922903121871646963927666306707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-29573006481942859668048187367437990000000000000)
      constant := (169499742813117881683964666751997736840894920453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550608311250223709/195312500000000000)
  centralHi := (281911455360114539009/100000000000000000000)
  directionLo := (286282436256548334439/100000000000000000000)
  directionHi := (7157060906413708361/2500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree034.table
  base := (-109191164727016602801995246293465537633/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-3429734720124095693483123873107500000000000)
      constant := (20203911287608589798433006579157456789804230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree034.table
  base := (-2737824047896882560015240964017747907/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-15321827307917847447688783311018735000000000000)
      constant := (91475738675585154291994733373067992345388202400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286282436256548334439/100000000000000000000)
  centralHi := (7157060906413708361/2500000000000000000)
  directionLo := (290587676880337560237/100000000000000000000)
  directionHi := (145293838440168780119/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree035.table
  base := (-9042309798622344760608002624669322959603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-28398214296650028945767640855100000000000000)
      constant := (174038194885024174673279118323327696868303493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree035.table
  base := (-9065131015678016667022252853848069723733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-63428605499457060245413891753273900000000000000)
      constant := (393903229707969066238619773205430371538994836307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290587676880337560237/100000000000000000000)
  centralHi := (145293838440168780119/50000000000000000000)
  directionLo := (73707514288079151429/25000000000000000000)
  directionHi := (294830057152316605717/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree036.table
  base := (-2329064037870492254379988629775064113199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-7339637708076823085917572681335000000000000)
      constant := (46732902092774548286393166872217937229030569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree036.table
  base := (-466823528128808428899919801892039728823/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-16392475441810682675018162565618215000000000000)
      constant := (105748908047579324085362455244422584616160302085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73707514288079151429/25000000000000000000)
  centralHi := (294830057152316605717/100000000000000000000)
  directionLo := (299012252668958507351/100000000000000000000)
  directionHi := (37376531583619813419/12500000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree037.table
  base := (-4779247205330419540845425411253542559413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 185000000000000000000000000000000000000000
      center := (1040)
      previous := (884)
      next := (0)
      square := (14122596112606814675038968680000000000000)
      linear := (-409714694161683185696931629670000000000000)
      constant := (2706887377608019192750295015653618925301719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree037.table
  base := (-9576386369638824765787357964252325772701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4558060)
      previous := (3942172)
      next := (0)
      square := (62393629625496907234322163628240000000000000)
      linear := (-1830032379325091923100848885720860000000000000)
      constant := (12248003722235736002219822243835274657619829167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299012252668958507351/100000000000000000000)
  centralHi := (37376531583619813419/12500000000000000000)
  directionLo := (303136754439134107273/100000000000000000000)
  directionHi := (151568377219567053637/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree038.table
  base := (-977019813099755485787146667693254356113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-15639611951810909569737795232910000000000000)
      constant := (107085380502067906378761399081179673932406515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree038.table
  base := (-1223252904063840890931829192873060058031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-17463123575703517902347541820217695000000000000)
      constant := (121110321076158475237543744451411912488494468498) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303136754439134107273/100000000000000000000)
  centralHi := (151568377219567053637/50000000000000000000)
  directionLo := (307205886235304254107/100000000000000000000)
  directionHi := (76801471558826063527/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree039.table
  base := (-12440473015083566414261572372189101081/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-4029945054909885317172280042007500000000000)
      constant := (28564188669900944496054362686199812062011100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree039.table
  base := (-4983183000964591586815869691329706307203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-35996895285299871032024462895034870000000000000)
      constant := (258394046814127872909607996345467382232554956437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307205886235304254107/100000000000000000000)
  centralHi := (76801471558826063527/25000000000000000000)
  directionLo := (311221819902373663357/100000000000000000000)
  directionHi := (155610909951186831679/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree040.table
  base := (-5052953211530535314765575415020761249087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-16599948487468172967640445103150000000000000)
      constant := (121668359188792170458342239486836577849999897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree040.table
  base := (-5059130982561376475097154424757359813567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-37067543419192706259353842149634350000000000000)
      constant := (275107001697243423227381500713313348283235950393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311221819902373663357/100000000000000000000)
  centralHi := (155610909951186831679/50000000000000000000)
  directionLo := (315186588910556782209/100000000000000000000)
  directionHi := (31518658891055678221/10000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree041.table
  base := (-10231532797303374221335152521728708877897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-34160233510593609333183540076540000000000000)
      constant := (258639360442246752158476358965973397546159007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree041.table
  base := (-32007625276518063492900538104093067521/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-19069095776542770743341610702116915000000000000)
      constant := (146179202280186443326699330612997714984426076720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315186588910556782209/100000000000000000000)
  centralHi := (31518658891055678221/10000000000000000000)
  directionLo := (319102100392333869463/100000000000000000000)
  directionHi := (39887762549041733683/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree042.table
  base := (-10329904333130586005625775337879544136641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-35120570046250872731086189946780000000000000)
      constant := (274420550086271680240547164038722904076938471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree042.table
  base := (-646220472704345129678646199308319866241/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-19604419843489188357006300329416655000000000000)
      constant := (155073653526199646103551073145395402671133603356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319102100392333869463/100000000000000000000)
  centralHi := (39887762549041733683/12500000000000000000)
  directionLo := (80742536466430571929/25000000000000000000)
  directionHi := (322970145865722287717/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree043.table
  base := (-10401578376471100927668173857129374669211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-36080906581908136128988839817020000000000000)
      constant := (290679524303083152482828897573769886077850141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree043.table
  base := (-10410064033430065126526590366246781170851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-80558975641742423882683959826865580000000000000)
      constant := (656945786398025154289924469537651987878824903029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80742536466430571929/25000000000000000000)
  centralHi := (322970145865722287717/100000000000000000000)
  directionLo := (326792410814958705071/100000000000000000000)
  directionHi := (20424525675934919067/6250000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree044.table
  base := (-5223517603914750216826625307386437805543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-18520621558782699763445744843630000000000000)
      constant := (153707812794335198442743107000147966644211633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree044.table
  base := (-163351778612283405934305317212050657297/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-20675067977382023584335679584016135000000000000)
      constant := (173667230450902962365612788066261288467269425008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (326792410814958705071/100000000000000000000)
  centralHi := (20424525675934919067/6250000000000000000)
  directionLo := (330570483273960119481/100000000000000000000)
  directionHi := (165285241636980059741/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree045.table
  base := (-2616672177812683633904113211252974281633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-9500394913305665731198534889375000000000000)
      constant := (81157071833943969220510646513669678208444423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree045.table
  base := (-10473276499914450161342661125211144009249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-84841568177313764792001476845263500000000000000)
      constant := (733462812054042751741258937067592099967605904871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330570483273960119481/100000000000000000000)
  centralHi := (165285241636980059741/50000000000000000000)
  directionLo := (334305861536567071607/100000000000000000000)
  directionHi := (41788232692070883951/12500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree046.table
  base := (-5230447782037267233651024274048407624227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-19480958094439963161348394713870000000000000)
      constant := (171158510626560750206751055422287729962433237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree046.table
  base := (-1046669584461933092115202355290950298643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-43491432222549717623330117677231230000000000000)
      constant := (386663208720692181975278373014164670459587160985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334305861536567071607/100000000000000000000)
  centralHi := (41788232692070883951/12500000000000000000)
  directionLo := (4224999513746887013/1250000000000000000)
  directionHi := (337999961099750961041/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree047.table
  base := (-5214981576491263700978316399628430903937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-19961126362268594860299719648990000000000000)
      constant := (180240703264170059939845099855998678092510247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree047.table
  base := (-10435067716408565897356578420593946132411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 643430000000000000000000000000000000000000000
      center := (3588260)
      previous := (3103412)
      next := (0)
      square := (49118389279646501439785533069040000000000000)
      linear := (-1896258738572023525559978592843860000000000000)
      constant := (17324656239916782091033368547497033724002279027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4224999513746887013/1250000000000000000)
  centralHi := (337999961099750961041/100000000000000000000)
  directionLo := (170827060465518731279/50000000000000000000)
  directionHi := (341654120931037462559/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree048.table
  base := (-5187078196602879589433165863145896075739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-20441294630097226559251044584110000000000000)
      constant := (189560540246240216763312072993993268272313309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree048.table
  base := (-2594661677096193666027653922675987093727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-22816364245167694038994438093215095000000000000)
      constant := (214064829909451961929020654666045851234131211033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170827060465518731279/50000000000000000000)
  centralHi := (341654120931037462559/100000000000000000000)
  directionLo := (172634804569419589179/50000000000000000000)
  directionHi := (345269609138839178359/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree049.table
  base := (-5146851801567515035512104245884557187801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-20921462897925858258202369519230000000000000)
      constant := (199117865288832717890288223101494041209900431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree049.table
  base := (-2059530383087519894483221891494673568571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-93406753248456446610636510882059340000000000000)
      constant := (899327183957084872449357295923969211365697494545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172634804569419589179/50000000000000000000)
  centralHi := (345269609138839178359/100000000000000000000)
  directionLo := (348847628113784925243/100000000000000000000)
  directionHi := (87211907028446231311/25000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree050.table
  base := (-10188801565393882677700118789381971178767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-42803262331508979914307388908700000000000000)
      constant := (417825087388483496823146667912336081456267977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree050.table
  base := (-10192271889012832482051981517605843398533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-95548049516242117065295269391258300000000000000)
      constant := (943461866031533032046369560748948799255784985507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348847628113784925243/100000000000000000000)
  centralHi := (87211907028446231311/25000000000000000000)
  directionLo := (352389319200143173761/100000000000000000000)
  directionHi := (176194659600071586881/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree051.table
  base := (-2011923977441875130408379242822769300197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-43763598867166243312210038778940000000000000)
      constant := (437888918732640773358175426924498144140151535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree051.table
  base := (-10062668899541447684511519353782745998451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-97689345784027787519954027900457260000000000000)
      constant := (988662875135734339008990741103708298388418363429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352389319200143173761/100000000000000000000)
  centralHi := (176194659600071586881/50000000000000000000)
  directionLo := (355895766948789659719/100000000000000000000)
  directionHi := (8897394173719741493/2500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree052.table
  base := (-4953152378616715300446424005718165574437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-22361967701411753355056344324590000000000000)
      constant := (229213512238936392352947117810211831328595747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree052.table
  base := (-4954491301703577077431663765616423942743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-49915321025906728987306393204828110000000000000)
      constant := (517464894465943017332707646740921754409848096097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355895766948789659719/100000000000000000000)
  centralHi := (8897394173719741493/2500000000000000000)
  directionLo := (359368002996641327617/100000000000000000000)
  directionHi := (179684001498320663809/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree053.table
  base := (-9728982182471110069698871140415309126337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-45684271938480770108015338519420000000000000)
      constant := (479439232120589600241587661063151441806044647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree053.table
  base := (-2432833299437374721161533294763883355853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-25492984579899782107317886229713795000000000000)
      constant := (270565560982323568757011032714743817802014469787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359368002996641327617/100000000000000000000)
  centralHi := (179684001498320663809/50000000000000000000)
  directionLo := (181403504805944156071/50000000000000000000)
  directionHi := (362807009611888312143/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree054.table
  base := (-4763880388677831200768726939637661809649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-23322304237069016752958994194830000000000000)
      constant := (250462696483816051491791310899896040982590519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree054.table
  base := (-4764912067363422303245459062893175069241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-52056617293692399441965151714027070000000000000)
      constant := (565329963638057230015755257918405418516431837839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181403504805944156071/50000000000000000000)
  centralHi := (362807009611888312143/100000000000000000000)
  directionLo := (366213722939552916481/100000000000000000000)
  directionHi := (183106861469776458241/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree055.table
  base := (-58142088543816867970246559339139919639/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-5950618126224412112977579782487500000000000)
      constant := (65360672355775758636394959963606849000284180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree055.table
  base := (-1860908891366093749904587084805823669883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-106254530855170469338589061937253100000000000000)
      constant := (1180122569697078825285570759028656888588048760785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366213722939552916481/100000000000000000000)
  centralHi := (183106861469776458241/50000000000000000000)
  directionLo := (23099314748610376957/6250000000000000000)
  directionHi := (369589035977766031313/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree056.table
  base := (-9053983058131572384590582254251246649507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-48565281545452560301723288130140000000000000)
      constant := (545319079268845560452726178266250043336824917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree056.table
  base := (-9055570806216504376596731996644980439997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-108395827122956139793247820446452060000000000000)
      constant := (1230649939417033523516052105139603665106815832363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23099314748610376957/6250000000000000000)
  centralHi := (369589035977766031313/100000000000000000000)
  directionLo := (46616725163946865379/12500000000000000000)
  directionHi := (372933801311574923033/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree057.table
  base := (-8781577023506744358833161812847602014697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-49525618081109823699625938000380000000000000)
      constant := (568226398990403173371649395556191632841879807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree057.table
  base := (-1097871144201015604131435371887669509977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-27634280847685452561976644738912755000000000000)
      constant := (320560459233132305255668525632975695487637689566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46616725163946865379/12500000000000000000)
  centralHi := (372933801311574923033/100000000000000000000)
  directionLo := (376248833627996845211/100000000000000000000)
  directionHi := (94062208406999211303/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree058.table
  base := (-1697115207963744001332163669088942747861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-50485954616767087097528587870620000000000000)
      constant := (591607255902800558217227751868566186890891455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree058.table
  base := (-8486796285945964110695185516126409386831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-112678419658527480702565337464849980000000000000)
      constant := (1334898090512986220797496359035952306718687249449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376248833627996845211/100000000000000000000)
  centralHi := (94062208406999211303/25000000000000000000)
  directionLo := (18976745601666981927/5000000000000000000)
  directionHi := (379534912033339638541/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree059.table
  base := (-8166031812869441385253389708995808649451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-51446291152424350495431237740860000000000000)
      constant := (615461579220794856313182049177204737958901581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree059.table
  base := (-1633420217296805046043421472739869341159/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-114819715926313151157224095974048940000000000000)
      constant := (1388618552329529543971589025592562097940724518805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18976745601666981927/5000000000000000000)
  centralHi := (379534912033339638541/100000000000000000000)
  directionLo := (382792782191464087497/100000000000000000000)
  directionHi := (191396391095732043749/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree060.table
  base := (-3911494459821688300658630710190589301107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-26203313844040806946666943805550000000000000)
      constant := (319894653959247165410715622854749083246784517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree060.table
  base := (-3911962818157829545306361069591524129717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-58480506097049410805941427241623950000000000000)
      constant := (721701547561920542565465505759211310457316096243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (382792782191464087497/100000000000000000000)
  centralHi := (191396391095732043749/50000000000000000000)
  directionLo := (77204631659922702681/20000000000000000000)
  directionHi := (193011579149806756703/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree061.table
  base := (-1864121448136678298135510303725256751013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-13341741055934719322809134370335000000000000)
      constant := (166147597345483727750719567118955123507863203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree061.table
  base := (-7457306162261707408682705986936438587933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-119102308461884492066541612992446860000000000000)
      constant := (1499251609341631173602069339271179020401021468107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77204631659922702681/20000000000000000000)
  centralHi := (193011579149806756703/50000000000000000000)
  directionLo := (389226724916641972901/100000000000000000000)
  directionHi := (194613362458320986451/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree062.table
  base := (-7066555567651670099398264910098183883701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-54327300759396140689139187351580000000000000)
      constant := (689864778247833729128018953941955586263213331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree062.table
  base := (-282690954102716359066347565959989492887/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-121243604729670162521200371501645820000000000000)
      constant := (1556164000665870917542901698971642385369526816825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389226724916641972901/100000000000000000000)
  centralHi := (194613362458320986451/50000000000000000000)
  directionLo := (98101034664224518411/25000000000000000000)
  directionHi := (78480827731379614729/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree063.table
  base := (-831653351969044305801318771804930164921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-6910954661881675510880229652727500000000000)
      constant := (89451554425346706567922387564971550604223151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree063.table
  base := (-831731944857691613130326350982686976209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-30846225249363958243964782502711195000000000000)
      constant := (403535046973497602065926963949331563857639725422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98101034664224518411/25000000000000000000)
  centralHi := (78480827731379614729/20000000000000000000)
  directionLo := (197778014880818399449/50000000000000000000)
  directionHi := (395556029761636798899/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree064.table
  base := (-1554131043108785362532669346376907507781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-14061993457677666871236121773015000000000000)
      constant := (185458331780159233394374830218090013621847811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree064.table
  base := (-3108537200119748125651321146809190423243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-62763098632620751715258944260021870000000000000)
      constant := (836590050555521578927870052998643684248071955597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197778014880818399449/50000000000000000000)
  centralHi := (395556029761636798899/100000000000000000000)
  directionLo := (79736600711722268627/20000000000000000000)
  directionHi := (12458843861206604473/3125000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree065.table
  base := (-5756468881124013790315647941227235935661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-57208310366367930882847136962300000000000000)
      constant := (768527424319176139941792280085959914004080091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree065.table
  base := (-359809392696446267472603961535126225173/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-31916873383256793471294161757310675000000000000)
      constant := (433320920029385467733499475563379667679214408268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79736600711722268627/20000000000000000000)
  centralHi := (12458843861206604473/3125000000000000000)
  directionLo := (200892820909709534089/50000000000000000000)
  directionHi := (401785641819419068179/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree066.table
  base := (-2636539630564768998024418673711792587821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-29084323451012597140374893416270000000000000)
      constant := (397847350959627553028971418546548555947273051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree066.table
  base := (-1318375087191959670891925673756185343053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-32452197450203211084958851384610415000000000000)
      constant := (448612718269109413202092565631204216024181218587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200892820909709534089/50000000000000000000)
  centralHi := (401785641819419068179/100000000000000000000)
  directionLo := (404864504023221725399/100000000000000000000)
  directionHi := (2024322520116108627/500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree067.table
  base := (-1191592777766508750028077402579796154609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-14782245859420614419663109175695000000000000)
      constant := (205833784573142706642243086567313259064340279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree067.table
  base := (-1191684839528812845117416599073993130001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-32987521517149628698623541011910155000000000000)
      constant := (464170408837168850672137229882888999321708245879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404864504023221725399/100000000000000000000)
  centralHi := (2024322520116108627/500000000000000000)
  directionLo := (203960064267307074557/50000000000000000000)
  directionHi := (81584025706922829823/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree068.table
  base := (-423635805656787855864092984814314282397/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-30044659986669860538277543286510000000000000)
      constant := (425724357392814921901366088633786018736992535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree068.table
  base := (-2118340011692488633933863090303884860687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-67045691168192092624576461278419790000000000000)
      constant := (959987964245512678678362172227825785411214368873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203960064267307074557/50000000000000000000)
  centralHi := (81584025706922829823/20000000000000000000)
  directionLo := (410953033702664052313/100000000000000000000)
  directionHi := (205476516851332026157/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree069.table
  base := (-3683051850000752776796080751506735325539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-61049656508996984474457736443260000000000000)
      constant := (880035415309443536219256397184607279339337109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree069.table
  base := (-920833323297124359884401911072559178993/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-34058169651042463925952920266509635000000000000)
      constant := (496083429848390403999026599057751048763064509847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410953033702664052313/100000000000000000000)
  centralHi := (205476516851332026157/50000000000000000000)
  directionLo := (413963718887476592273/100000000000000000000)
  directionHi := (206981859443738296137/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree070.table
  base := (-3106462628799587626342575570905550002371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-62009993044654247872360386313500000000000000)
      constant := (909095225985863484687198976680430302046754101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree070.table
  base := (-3106708598024038592763664682316989441667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-138373974871955526158470439575237500000000000000)
      constant := (2049754979537316450788676817272392363572676550293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413963718887476592273/100000000000000000000)
  centralHi := (206981859443738296137/50000000000000000000)
  directionLo := (416952665420040878083/100000000000000000000)
  directionHi := (104238166355010219521/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree071.table
  base := (-78331223067126988733955635050146407237/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-7871291197538938908782879522967500000000000)
      constant := (117328516855341653819746209310017898273970188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree071.table
  base := (-501362812310519247936514657946513342879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-140515271139741196613129198084436460000000000000)
      constant := (2116239684355356048325277330833005990615097078205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416952665420040878083/100000000000000000000)
  centralHi := (104238166355010219521/25000000000000000000)
  directionLo := (209960168750291396857/50000000000000000000)
  directionHi := (83984067500116558743/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree072.table
  base := (-235433615365577624736785990362613692717/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-7991333264496096833520710756747500000000000)
      constant := (121079266443889273652858434059653581854670427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree072.table
  base := (-376731336488487223145500201909330712413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-142656567407526867067787956593635420000000000000)
      constant := (2183787812682860734161804050849511084483234430135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (209960168750291396857/50000000000000000000)
  centralHi := (83984067500116558743/20000000000000000000)
  directionLo := (422867183040171808513/100000000000000000000)
  directionHi := (211433591520085904257/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree073.table
  base := (-247415698631849038370391527741135796521/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-64891002651626038066068335924220000000000000)
      constant := (999113207198775310545690481739391925472813755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree073.table
  base := (-1237242490884395640042756201982410362741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-144797863675312537522446715102834380000000000000)
      constant := (2252399346283803762851436872379281221191417324339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422867183040171808513/100000000000000000000)
  centralHi := (211433591520085904257/50000000000000000000)
  directionLo := (425793634449902240309/100000000000000000000)
  directionHi := (42579363444990224031/10000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree074.table
  base := (-567433466658792195258619840572501516383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (2080)
      previous := (1768)
      next := (0)
      square := (28245192225213629350077937360000000000000)
      linear := (-1779765923980629769296513129580000000000000)
      constant := (27839604164728081316166781883458817443893829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree074.table
  base := (-283788341654074169539939150567524543691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 408665000000000000000000000000000000000000000
      center := (2279030)
      previous := (1971086)
      next := (0)
      square := (31196814812748453617161081814120000000000000)
      linear := (-1985664323555381188879803697459910000000000000)
      constant := (31379382019507473427833643777531634516470503497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425793634449902240309/100000000000000000000)
  centralHi := (42579363444990224031/10000000000000000000)
  directionLo := (428700109381585980233/100000000000000000000)
  directionHi := (214350054690792990117/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree075.table
  base := (7841331752923628466046032029960237871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-8351459465367570607734204458087500000000000)
      constant := (132686320700245971065917191304760531131290798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree075.table
  base := (125336261662702017557812036493855406757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-149080456210883878431764232121232300000000000000)
      constant := (2392812568618208855331225788656630084506537385597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428700109381585980233/100000000000000000000)
  centralHi := (214350054690792990117/50000000000000000000)
  directionLo := (431587011423548972947/100000000000000000000)
  directionHi := (107896752855887243237/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree076.table
  base := (1346562633152640900436413613900752083/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-67772012258597828259776285534940000000000000)
      constant := (1093388835990272048051583551853513831001016875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree076.table
  base := (84149248340242306371418834049652370683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-75610876239334774443211495315215630000000000000)
      constant := (1232307116066385938738586444199666283884411223215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431587011423548972947/100000000000000000000)
  centralHi := (107896752855887243237/25000000000000000000)
  directionLo := (54306841344351674309/12500000000000000000)
  directionHi := (434454730754813394473/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree077.table
  base := (790491966527287675256285029902779618799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-34366174397127545828839467702590000000000000)
      constant := (562880080156616939901761425284726905298135831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree077.table
  base := (158088865337206264288941284495427712723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-76681524373227609670540874569815110000000000000)
      constant := (1268739624960668777781532246440470321750137957415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54306841344351674309/12500000000000000000)
  centralHi := (434454730754813394473/100000000000000000000)
  directionLo := (218651822380333825249/50000000000000000000)
  directionHi := (437303644760667650499/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree078.table
  base := (2343605049910566846461797035482579609643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-69692685329912355055581585275420000000000000)
      constant := (1158604534299383334784793948401455651485601267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree078.table
  base := (2343521901169310769788649029909726503889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-155504345014240889795740507648829180000000000000)
      constant := (2611407613303461985513860795789884252024667306569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218651822380333825249/50000000000000000000)
  centralHi := (437303644760667650499/100000000000000000000)
  directionLo := (110033529653093417699/25000000000000000000)
  directionHi := (440134118612373670797/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree079.table
  base := (3129462301420709160668014854419567222353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-70653021865569618453484235145660000000000000)
      constant := (1191921954259446578392051976097720387527401257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree079.table
  base := (1564694875436522416693279748467128610881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-78822820641013280125199633079014070000000000000)
      constant := (1343199657395830053048992621383745026441866060601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110033529653093417699/25000000000000000000)
  centralHi := (440134118612373670797/100000000000000000000)
  directionLo := (442946505813532547871/100000000000000000000)
  directionHi := (13842078306672892121/3125000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree080.table
  base := (984638339863648774981267124152516743863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-17903339600306720462846721253975000000000000)
      constant := (306428104251553270794449426858964795422348447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree080.table
  base := (984622516562132436873537449902532284063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-39946734387453057676264506166806775000000000000)
      constant := (690613586981424898502964221434865695833412883623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442946505813532547871/100000000000000000000)
  centralHi := (13842078306672892121/3125000000000000000)
  directionLo := (222870574357711381071/50000000000000000000)
  directionHi := (445741148715422762143/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree081.table
  base := (4770876212156938003613074440238583574729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-72573694936884145249289534886140000000000000)
      constant := (1259975919785452961703642521874506620913804001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree081.table
  base := (2385410501789549136112057240586811591253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-80964116908798950579858391588213030000000000000)
      constant := (1419786353564979078902660243320294344256151613613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222870574357711381071/50000000000000000000)
  centralHi := (445741148715422762143/100000000000000000000)
  directionLo := (448518379003437761027/100000000000000000000)
  directionHi := (112129594750859440257/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree082.table
  base := (225057164817732254526483080335853151603/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-73534031472541408647192184756380000000000000)
      constant := (1294712460216359627234354150091974574113612675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree082.table
  base := (5626380971062122312804235736614957735849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-164069530085383571614375541685625020000000000000)
      constant := (2917754387590632042001785391390163782603093413729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448518379003437761027/100000000000000000000)
  centralHi := (112129594750859440257/25000000000000000000)
  directionLo := (90255703631315898549/20000000000000000000)
  directionHi := (225639259078289746373/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree083.table
  base := (406575661280856000311973972514349816437/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-9311796001024834005636854328327500000000000)
      constant := (166240254530025436757037612207866789797404506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree083.table
  base := (6505168593855092351088573868162783181419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-166210826353169242069034300194823980000000000000)
      constant := (2996999385150031141874726582683424074037376007699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90255703631315898549/20000000000000000000)
  centralHi := (225639259078289746373/50000000000000000000)
  directionLo := (227010938940904924173/50000000000000000000)
  directionHi := (454021877881809848347/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree084.table
  base := (3703609645708215211822275452336402549923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-37727352271927967721498742248430000000000000)
      constant := (682802323038031928516756036229408535090844587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree084.table
  base := (7407182683984994843517041690150857371219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-168352122620954912523693058704022940000000000000)
      constant := (3077307696215581319733779586100365380944308173499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227010938940904924173/50000000000000000000)
  centralHi := (454021877881809848347/100000000000000000000)
  directionLo := (114187190131230313137/25000000000000000000)
  directionHi := (456748760524921252549/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree085.table
  base := (8332454127369102273822266450707767196807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-76415041079513198840900134367100000000000000)
      constant := (1401760288182662460510273736942518933292428783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree085.table
  base := (2083105553610948702068793093288681902833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-42623354722185145744587954303305475000000000000)
      constant := (789669829420371502455426163599580449504677234793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/25000000000000000000)
  centralHi := (456748760524921252549/100000000000000000000)
  directionLo := (459459459459459459459/100000000000000000000)
  directionHi := (22972972972972972973/5000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree086.table
  base := (4640457056760858789684875330617728464987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-38687688807585231119401392118670000000000000)
      constant := (719194480612728521366614862063875670268567203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree086.table
  base := (1856177259377433887502401881924203004189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-172634715156526253433010575722420860000000000000)
      constant := (3241114246861284490304500745132714493566155214345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459459459459459459459/100000000000000000000)
  centralHi := (22972972972972972973/5000000000000000000)
  directionLo := (462154259455114703643/100000000000000000000)
  directionHi := (115538564863778675911/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree087.table
  base := (10252598405332058539402617029343995775529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-78335714150827725636705434107580000000000000)
      constant := (1475490664048269307532969308886551930216699201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree087.table
  base := (32039294257608841321353827349017884763/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-43694002856077980971917333557904955000000000000)
      constant := (831153120357447432798438223643277237674989465840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462154259455114703643/100000000000000000000)
  centralHi := (115538564863778675911/25000000000000000000)
  directionLo := (232416718513445309303/50000000000000000000)
  directionHi := (464833437026890618607/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree088.table
  base := (11247506270676419130154277828282292369483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-79296050686484989034608083977820000000000000)
      constant := (1513065395648821901362956032620998458253822227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree088.table
  base := (11247485145140639197741432554494707784923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-176917307692097594342328092740818780000000000000)
      constant := (3409174019373100040868442061740979010201249127683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232416718513445309303/50000000000000000000)
  centralHi := (464833437026890618607/100000000000000000000)
  directionLo := (467497260766262773007/100000000000000000000)
  directionHi := (29218578797891423313/6250000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree089.table
  base := (191650579288154821001946586347089052927/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-10032048402767781554063841731007500000000000)
      constant := (193889144394705659588465273485500819307656504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree089.table
  base := (12265618667760892058996764505742638365167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-179058603959883264796986851250017740000000000000)
      constant := (3494798858945560601954987192835847563275507193207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467497260766262773007/100000000000000000000)
  centralHi := (29218578797891423313/6250000000000000000)
  directionLo := (117536497913862351399/25000000000000000000)
  directionHi := (470145991655449405597/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree090.table
  base := (13306990265240855651552773565331038073391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-81216723757799515830413383718300000000000000)
      constant := (1589633941819889711790625301685938191122472279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree090.table
  base := (6653487114750422300435150978542372510457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-90599950113834467625822804879608350000000000000)
      constant := (1790743499316353757417668072332981788098695733297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117536497913862351399/25000000000000000000)
  centralHi := (470145991655449405597/100000000000000000000)
  directionLo := (236389941682917586657/50000000000000000000)
  directionHi := (94555976673167034663/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree091.table
  base := (14371565363954685097966366781410984762777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-82177060293456779228316033588540000000000000)
      constant := (1628627754979641876951392539098971638140241713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree091.table
  base := (7185775697732088590813754844565956767999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-91670598247727302853152184134207830000000000000)
      constant := (1834619218559680843229103516424566410747197903879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236389941682917586657/50000000000000000000)
  centralHi := (94555976673167034663/20000000000000000000)
  directionLo := (475399182541513756331/100000000000000000000)
  directionHi := (118849795635378439083/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree092.table
  base := (966210122115938014453668469499368344231/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-10392174603639255328277335432347500000000000)
      constant := (208511824258300076015661234353899270526504478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree092.table
  base := (3091869957513675601764503178404717332529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-185482492763240276160963126777614620000000000000)
      constant := (3758053173262155853179316655081847980921824660045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475399182541513756331/100000000000000000000)
  centralHi := (118849795635378439083/25000000000000000000)
  directionLo := (478004129068846355907/100000000000000000000)
  directionHi := (119501032267211588977/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree093.table
  base := (16570379672084472506610800065084709902057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-84097733364771306024121333329020000000000000)
      constant := (1708034458583414189678460153064280967855916033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree093.table
  base := (16570369076722054860928022201974245392061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-187623789031025946615621885286813580000000000000)
      constant := (3847931206065877824862307656308919626949284903381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478004129068846355907/100000000000000000000)
  centralHi := (119501032267211588977/25000000000000000000)
  directionLo := (30037184770804369249/6250000000000000000)
  directionHi := (96118991266573981597/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree094.table
  base := (17704618202309910726086459875906473344549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-85058069900428569422023983199260000000000000)
      constant := (1748447348097622515716928687845035962008687581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree094.table
  base := (3540921795217716163723698281253549497831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 643430000000000000000000000000000000000000000
      center := (3588260)
      previous := (3103412)
      next := (0)
      square := (49118389279646501439785533069040000000000000)
      linear := (-4037555006357693980218737102042820000000000000)
      constant := (83805798609853168818537922842746625676694700165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30037184770804369249/6250000000000000000)
  centralHi := (96118991266573981597/20000000000000000000)
  directionLo := (241585945730665353601/50000000000000000000)
  directionHi := (483171891461330707203/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree095.table
  base := (9431038634193094759941890360839624163961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-43009203218042916409963316534750000000000000)
      constant := (894666631115491449328718342991239445480462609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree095.table
  base := (18862069235284928232533164372013652377589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-191906381566597287524939402305211500000000000000)
      constant := (4030877158296630610048228298712647548441766824269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241585945730665353601/50000000000000000000)
  centralHi := (483171891461330707203/100000000000000000000)
  directionLo := (485735155557065633989/100000000000000000000)
  directionHi := (48573515555706563399/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree096.table
  base := (20042756628891446360188531442842723820623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-86978742971743096217829282939740000000000000)
      constant := (1830692200652988808699406465019171688910432887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree096.table
  base := (20042749635385587771463996191380918206053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-194047677834382957979598160814410460000000000000)
      constant := (4123945076304415621388943227644873133746207204413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485735155557065633989/100000000000000000000)
  centralHi := (48573515555706563399/10000000000000000000)
  directionLo := (244142481959701944321/50000000000000000000)
  directionHi := (488284963919403888643/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree097.table
  base := (5311664018103404668456859699938625735669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-21984769876850089903932983202495000000000000)
      constant := (468131040768554283045040953472510978632130861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree097.table
  base := (21246649984619581393450487606736785060109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-196188974102168628434256919323609420000000000000)
      constant := (4218076288106515326606195533430276523172761889189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244142481959701944321/50000000000000000000)
  centralHi := (488284963919403888643/100000000000000000000)
  directionLo := (490821526255216688647/100000000000000000000)
  directionHi := (61352690781902086081/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree098.table
  base := (22473775413484731818709672477821715016729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-88899416043057623013634582680220000000000000)
      constant := (1914829149240762211814686385894417927857902001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree098.table
  base := (22473770114664167751258424806472411793481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-198330270369954298888915677832808380000000000000)
      constant := (4313270793193901388814245938162681376425313555201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490821526255216688647/100000000000000000000)
  centralHi := (61352690781902086081/12500000000000000000)
  directionLo := (98669009376040088653/20000000000000000000)
  directionHi := (246672523440100221633/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree099.table
  base := (7591716636503581030030286366719400579/3200000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-89859752578714886411537232550460000000000000)
      constant := (1957607158929434478443943066633841435602034375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree099.table
  base := (11862054938726128633215309407837832672937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-100235783318869984671787218171003670000000000000)
      constant := (2204764295559400506505000454531043719380714913377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98669009376040088653/20000000000000000000)
  centralHi := (246672523440100221633/50000000000000000000)
  directionLo := (247927862455470089611/50000000000000000000)
  directionHi := (495855724910940179223/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree100.table
  base := (12498836577780314098229077892903194494859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-45410044557186074904719941210350000000000000)
      constant := (1000429095971809166950780487970384473263461971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree100.table
  base := (24997669142422104295539888350938703703343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-202612862905525639798233194851206300000000000000)
      constant := (4506849681486379682396513795238534103582057336503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247927862455470089611/50000000000000000000)
  centralHi := (495855724910940179223/100000000000000000000)
  directionLo := (498353754448264178919/100000000000000000000)
  directionHi := (12458843861206604473/2500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree101.table
  base := (13147225643063236668028575684910293437713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-45890212825014706603671266145470000000000000)
      constant := (1022291124054849235052115061596952191716229097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree101.table
  base := (5258889558829557147894732316264749842591/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-204754159173311310252891953360405260000000000000)
      constant := (4605234063947575438985373186854073987793630687555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498353754448264178919/100000000000000000000)
  centralHi := (12458843861206604473/2500000000000000000)
  directionLo := (62604915594045957469/12500000000000000000)
  directionHi := (500839324752367659753/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree102.table
  base := (6903612192125137468445557790940109602639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-23185190546421669151311295540295000000000000)
      constant := (522194831818494082811681747282567010046012791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree102.table
  base := (27614445730297533116018676701749830346979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-206895455441096980707550711869604220000000000000)
      constant := (4704681738192924632742379832405463818698736480459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62604915594045957469/12500000000000000000)
  centralHi := (500839324752367659753/100000000000000000000)
  directionLo := (251656310205076322399/50000000000000000000)
  directionHi := (503312620410152644799/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree103.table
  base := (28957665503016899590128721205440165552803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-93701098721343940003147832031420000000000000)
      constant := (2133449429300009220526549675095627586641787307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree103.table
  base := (3619707857484293915167996886294464607359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-52259187927220662790552367594700795000000000000)
      constant := (1201298175986810334959285337368550497705742212878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251656310205076322399/50000000000000000000)
  centralHi := (503312620410152644799/100000000000000000000)
  directionLo := (20230952859808109891/4000000000000000000)
  directionHi := (126443455373800686819/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree104.table
  base := (15162050700468411540509194557580286012191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-47330717628500601700525240950830000000000000)
      constant := (1089296277033156929229757540481087411550689479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree104.table
  base := (30324099101699697980619437270654116436251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-211178047976668321616868228888002140000000000000)
      constant := (4906766960965031825524544102318934277251311810371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20230952859808109891/4000000000000000000)
  centralHi := (126443455373800686819/25000000000000000000)
  directionLo := (254111551860392614291/50000000000000000000)
  directionHi := (508223103720785228583/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree105.table
  base := (31713756383000990148828199175129134043783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-95621771792658466798953131771900000000000000)
      constant := (2224208701464384222005077270832251784505938927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree105.table
  base := (31713754383106455248862143416640658241553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-213319344244453992071526987397201100000000000000)
      constant := (5009404509026541932720100498452524514042103499913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254111551860392614291/50000000000000000000)
  centralHi := (508223103720785228583/100000000000000000000)
  directionLo := (510660638586248223813/100000000000000000000)
  directionHi := (255330319293124111907/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree106.table
  base := (8281657594544880934608361008238077611349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-24145527082078932549213945410535000000000000)
      constant := (567574467849245102368692630085107928249936781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree106.table
  base := (33126628638812124092205938314236945700237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-215460640512239662526185745906400060000000000000)
      constant := (5113105347934349485163016186702818726467946416677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (510660638586248223813/100000000000000000000)
  centralHi := (255330319293124111907/50000000000000000000)
  directionLo := (256543296758579153209/50000000000000000000)
  directionHi := (513086593517158306419/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree107.table
  base := (6912544664518563267969505527360203715609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-97542444863972993594758431512380000000000000)
      constant := (2316860063776651238187423179491760594433343605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree107.table
  base := (17281360904973607628416030727049543147917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-108800968390012666490422252207799510000000000000)
      constant := (2608934738755213012070771761609769676474021905957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256543296758579153209/50000000000000000000)
  centralHi := (513086593517158306419/100000000000000000000)
  directionLo := (515501131999502445437/100000000000000000000)
  directionHi := (257750565999751222719/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree108.table
  base := (1125688598705612256199936396881848580917/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-12312847674953782124082635172827500000000000)
      constant := (295486909815557302704361076991135002829101492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree108.table
  base := (36022033843217292380907769332057308141537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-219743233047811003435503262924797980000000000000)
      constant := (5323696897593602725470700509884112998754293013977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515501131999502445437/100000000000000000000)
  centralHi := (257750565999751222719/50000000000000000000)
  directionLo := (517904413708258767537/100000000000000000000)
  directionHi := (258952206854129383769/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree109.table
  base := (18752282916945982681526100481420400054879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-49731558967643760195281865626430000000000000)
      constant := (1205701757784437301975101631434974527675129351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree109.table
  base := (18752282345090059702021726220110415053613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-110942264657798336945081010716998470000000000000)
      constant := (2715293804018692202896652830200963743482347199173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517904413708258767537/100000000000000000000)
  centralHi := (258952206854129383769/50000000000000000000)
  directionLo := (130074148657655563929/25000000000000000000)
  directionHi := (520296594630622255717/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree110.table
  base := (39010315301000033979278111610993071546551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-100423454470944783788466381123100000000000000)
      constant := (2459384774844831349494512641444449514947228319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree110.table
  base := (9752578576655486010692937426670075761771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-56006456395845586086205194985798975000000000000)
      constant := (1384635402177015832085031843835209811182762678291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130074148657655563929/25000000000000000000)
  centralHi := (520296594630622255717/100000000000000000000)
  directionLo := (3266736419900965571/625000000000000000)
  directionHi := (522677827184154491361/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree111.table
  base := (40539283516490956856815763718884254185199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (2080)
      previous := (1768)
      next := (0)
      square := (28245192225213629350077937360000000000000)
      linear := (-2740102459637893167199162999820000000000000)
      constant := (67779433953862066991306781175058717404852363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree111.table
  base := (10134820663004792424465930221813550516739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204332500000000000000000000000000000000000000
      center := (1139515)
      previous := (985543)
      next := (0)
      square := (15598407406374226808580540907060000000000000)
      linear := (-1528156228724108208104591476029695000000000000)
      constant := (38159181753264129957026411031761309424384628687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3266736419900965571/625000000000000000)
  centralHi := (522677827184154491361/100000000000000000000)
  directionLo := (262524130165055339659/50000000000000000000)
  directionHi := (525048260330110679319/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree112.table
  base := (8418294088109906456652099176644250696749/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-102344127542259310584271680863580000000000000)
      constant := (2556766359858562980357436067507009896019246905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree112.table
  base := (42091469689073579721793660411752838784571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-228308418118953685254138296961593820000000000000)
      constant := (5757639480249673801466317948226803526578035637091) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262524130165055339659/50000000000000000000)
  centralHi := (525048260330110679319/100000000000000000000)
  directionLo := (527408039682182398531/100000000000000000000)
  directionHi := (131852009920545599633/25000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree113.table
  base := (43666876036509087058301447944929116676471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-103304464077916573982174330733820000000000000)
      constant := (2606166685491634178920542565976187960730088799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree113.table
  base := (43666875383310923524184693983637984632919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-230449714386739355708797055470792780000000000000)
      constant := (5868783350903556726649733618444706955726087639199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527408039682182398531/100000000000000000000)
  centralHi := (131852009920545599633/25000000000000000000)
  directionLo := (16554915862840022259/3125000000000000000)
  directionHi := (529757307610880712289/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree114.table
  base := (45265500270463025226522187497202217118109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-104264800613573837380076980604060000000000000)
      constant := (2656040033145691944504705302919789835234691221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree114.table
  base := (45265499702734090560737591260964373918147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-232591010654525026163455813979991740000000000000)
      constant := (5980990511347976875253819110593470223417720623787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16554915862840022259/3125000000000000000)
  centralHi := (529757307610880712289/100000000000000000000)
  directionLo := (106419240668754275667/20000000000000000000)
  directionHi := (16628006354492855573/3125000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree115.table
  base := (46887343110928714984391715487351495241031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-105225137149231100777979630474300000000000000)
      constant := (2706386402777636554170890340634684196984971439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree115.table
  base := (23443671308761658855949085679943644681319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-117366153461155348309057286244595350000000000000)
      constant := (3047130480746377837706852557812229979697315095599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106419240668754275667/20000000000000000000)
  centralHi := (16628006354492855573/3125000000000000000)
  directionLo := (534424863061761851663/100000000000000000000)
  directionHi := (33401553941360115729/6250000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree116.table
  base := (12133101132139134508852545270117149150027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-26546368421222091043970570086135000000000000)
      constant := (689301448586822095117797345831970377186386963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree116.table
  base := (48532404099776925348121505584657351154337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-236873603190096367072773330998389660000000000000)
      constant := (6208594701253515071826412594225357853430204762777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534424863061761851663/100000000000000000000)
  centralHi := (33401553941360115729/6250000000000000000)
  directionLo := (536743419991628509503/100000000000000000000)
  directionHi := (8386615937369195461/1562500000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree117.table
  base := (50200684495877913529837855548192588530233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-107145810220545627573784930214780000000000000)
      constant := (2808498207817042936222308742370255653697888977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree117.table
  base := (25100342061643490557907052478958370846553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-119507449728941018763716044753794310000000000000)
      constant := (3161995865275499552947430025458233802402848704913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536743419991628509503/100000000000000000000)
  centralHi := (8386615937369195461/1562500000000000000)
  directionLo := (269526002247480995713/50000000000000000000)
  directionHi := (539052004494961991427/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree118.table
  base := (12973045746771740107697159318821071016613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-27026536689050722742921895021255000000000000)
      constant := (715065910787892992571187836162636046221743197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree118.table
  base := (25946091331672534245284735343561378799827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-120578097862833853991045424008393790000000000000)
      constant := (3220226024655243268165421390081393090417511627067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269526002247480995713/50000000000000000000)
  centralHi := (539052004494961991427/100000000000000000000)
  directionLo := (541350744153698684927/100000000000000000000)
  directionHi := (132165709021899093/24414062500000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree119.table
  base := (53606899977851196471561785393605668071207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-109066483291860154369590229955260000000000000)
      constant := (2912502100317564314435403875920266159589482383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree119.table
  base := (5360689969657400693071621142278122807959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-121648745996726689218374803262993270000000000000)
      constant := (3278987828730640970268750476142544960120638895195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541350744153698684927/100000000000000000000)
  centralHi := (132165709021899093/24414062500000000)
  directionLo := (543639763852397149857/100000000000000000000)
  directionHi := (271819881926198574929/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree120.table
  base := (55344835445147304995203695370021508798849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-110026819827517417767492879825500000000000000)
      constant := (2965213579283501048170896851573559445545624281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree120.table
  base := (55344835200781947086914494688213898815197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-245438788261239048891408365035185500000000000000)
      constant := (6676562554936274480868659643754174103898912366837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543639763852397149857/100000000000000000000)
  centralHi := (271819881926198574929/50000000000000000000)
  directionLo := (5459191858574096191/1000000000000000000)
  directionHi := (545919185857409619101/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree121.table
  base := (11421197873423709369897112581528884791003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-110987156363174681165395529695740000000000000)
      constant := (3018398080019460295591829038527985216394415535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree121.table
  base := (57105989154835760948194479589540521904423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-247580084529024719346067123544384460000000000000)
      constant := (6796212741671555021110656728356196702642125587183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5459191858574096191/1000000000000000000)
  centralHi := (545919185857409619101/100000000000000000000)
  directionLo := (54818912989309059681/10000000000000000000)
  directionHi := (548189129893090596811/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree122.table
  base := (58890361722950865177425500857026170228597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-111947492898831944563298179565980000000000000)
      constant := (3072055602496947612860992233275948827042949293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree122.table
  base := (29445180769275537096062241970547849455259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-124860690398405194900362941026791710000000000000)
      constant := (3458463108803041785501582892464080543042487302339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54818912989309059681/10000000000000000000)
  centralHi := (548189129893090596811/100000000000000000000)
  directionLo := (550449713215176961503/100000000000000000000)
  directionHi := (17201553537974280047/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree123.table
  base := (30348976246382568382489306440131485275469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-56453914717244603980600414718110000000000000)
      constant := (1563093073344374240149179486365430003342117061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree123.table
  base := (60697952332596655963847729583755908305729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-251862677064596060255384640562782380000000000000)
      constant := (7038702982681400149362166478646720471181429489209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550449713215176961503/100000000000000000000)
  centralHi := (17201553537974280047/3125000000000000000)
  directionLo := (552701050681466834447/100000000000000000000)
  directionHi := (34543815667591677153/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree124.table
  base := (62528761657523373523304014994787547066879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-113868165970146471359103479306460000000000000)
      constant := (3180789712568799892210306086720584151934557351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree124.table
  base := (500230092147289584842920539529092946691/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-254003973332381730710043399071981340000000000000)
      constant := (7161543036841373114399582264807849791380016701375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552701050681466834447/100000000000000000000)
  centralHi := (34543815667591677153/6250000000000000000)
  directionLo := (554943254819917761861/100000000000000000000)
  directionHi := (277471627409958880931/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree125.table
  base := (4023924324934186212501033373737102034643/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-14353562813225466844625766147087500000000000)
      constant := (404483287514009806325139784138229685370852534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree125.table
  base := (1609569726953269715284637931906551419519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-64036317400041850291175539395295075000000000000)
      constant := (1821361595007994958669515144741581409353472177990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554943254819917761861/100000000000000000000)
  centralHi := (277471627409958880931/50000000000000000000)
  directionLo := (278588217947139226339/50000000000000000000)
  directionHi := (557176435894278452679/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree126.table
  base := (517656524214417407626597497610805236911/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-14473604880182624769363597380867500000000000)
      constant := (411426988661812840634638178510432077909298544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree126.table
  base := (33130017497262809464596937509743813552301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-129143282933976535809680458045189630000000000000)
      constant := (3705206506100557642163677882737925161183598052421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278588217947139226339/50000000000000000000)
  centralHi := (557176435894278452679/100000000000000000000)
  directionLo := (139850175491840596137/25000000000000000000)
  directionHi := (559400701967362384549/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree127.table
  base := (68160499342053951941718157700448258408011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-116749175577118261552811428917180000000000000)
      constant := (3347438540092847948369272619968493665760567059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree127.table
  base := (13632099850188933384452849781642372071873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-260427862135738742074019674599578220000000000000)
      constant := (7536442933298424757632935008013413729361823243165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139850175491840596137/25000000000000000000)
  centralHi := (559400701967362384549/100000000000000000000)
  directionLo := (561616158962066013931/100000000000000000000)
  directionHi := (140404039740516503483/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree128.table
  base := (14016836382075804697691654473992601556979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-117709512112775524950714078787420000000000000)
      constant := (3403934192484671381729731913045359357657521255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree128.table
  base := (70084181831267271421578986660633700535357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-262569158403524412528678433108777180000000000000)
      constant := (7663536143275157424619687474942923367096684346197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561616158962066013931/100000000000000000000)
  centralHi := (140404039740516503483/25000000000000000000)
  directionLo := (563822910720229078017/100000000000000000000)
  directionHi := (281911455360114539009/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree129.table
  base := (18007770697137645669343588350585837715101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-29667462162108197087154182164415000000000000)
      constant := (865225716612061728207030803368207011831973269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree129.table
  base := (36015541359930332101810834173733736186221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-132355227335655041491668595808988070000000000000)
      constant := (3895846321042018951307372233455703955009210836741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563822910720229078017/100000000000000000000)
  centralHi := (281911455360114539009/50000000000000000000)
  directionLo := (113204211811885907/20000000000000000)
  directionHi := (566021059059429535001/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree130.table
  base := (37000600980590050344941989365980872607889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-59815092592045025873259689263950000000000000)
      constant := (1759172280981253822855903592721527814600200041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree130.table
  base := (37000600950771327162314991314276816441637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-133425875469547876718997975063587550000000000000)
      constant := (3960456214839576704579532279593276370414299726077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113204211811885907/20000000000000000)
  centralHi := (566021059059429535001/100000000000000000000)
  directionLo := (284105351913900517411/50000000000000000000)
  directionHi := (568210703827801034823/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree131.table
  base := (37997269706661850066342440049213740725419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-60295260859873657572211014199070000000000000)
      constant := (1788129639503497706114676511853783611053098611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree131.table
  base := (75994539361548770903493723570061274696433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-268993047206881423892654708636374060000000000000)
      constant := (8051195506015854397807193874689535202096251660393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284105351913900517411/50000000000000000000)
  centralHi := (568210703827801034823/100000000000000000000)
  directionLo := (570391942956956426059/100000000000000000000)
  directionHi := (28519597147847821303/5000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree132.table
  base := (7801109513044965595440922794912384959977/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-60775429127702289271162339134190000000000000)
      constant := (1817323508780908140392719084804415275051042565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree132.table
  base := (78011095085503266174117125813991548055969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-271134343474667094347313467145573020000000000000)
      constant := (8182541871050666867848979121390158454298565028249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570391942956956426059/100000000000000000000)
  centralHi := (28519597147847821303/5000000000000000000)
  directionLo := (572564872513096668879/100000000000000000000)
  directionHi := (7157060906413708361/1250000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree133.table
  base := (20012717274602423601289530817920885688547/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-30627798697765460485056832034655000000000000)
      constant := (923376944401900316154112757599728692507620843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree133.table
  base := (40025434529696731534318548143461757124713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-136637819871226382400986112827385990000000000000)
      constant := (4157475762370607394148638547200067847417744202273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572564872513096668879/100000000000000000000)
  centralHi := (7157060906413708361/1250000000000000000)
  directionLo := (114945917349276124559/20000000000000000000)
  directionHi := (143682396686595155699/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree134.table
  base := (20528465325853396713323738645954866692103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-30867882831679776334532494502215000000000000)
      constant := (938210389781367885181420271239642212501489007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree134.table
  base := (41056930634773501296696591798321045334301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-137708468005119217628315492081985470000000000000)
      constant := (4224212233523075645599910177897395027937411674421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114945917349276124559/20000000000000000000)
  centralHi := (143682396686595155699/25000000000000000000)
  directionLo := (288443089069313748189/50000000000000000000)
  directionHi := (576886178138627496379/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree135.table
  base := (42100035866003301958054298527778220198221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-62215933931188184368016313939550000000000000)
      constant := (1906324181048503792294098401697778383451364549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree135.table
  base := (3368002868104464296427310690530224238763/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-277558232278024105711289742673169900000000000000)
      constant := (8582960697925097474261838319225851056378805058075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288443089069313748189/50000000000000000000)
  centralHi := (576886178138627496379/100000000000000000000)
  directionLo := (144758684362355067527/25000000000000000000)
  directionHi := (579034737449420270109/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree136.table
  base := (3452380014841978182768099365923827513133/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-125392204398033632133935277749340000000000000)
      constant := (3872928186504221706791599286118262996636976925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree136.table
  base := (43154750172768515355219673676203143177401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-139849764272904888082974250591184430000000000000)
      constant := (4359280108669293906024912935422664365548785089521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144758684362355067527/25000000000000000000)
  centralHi := (579034737449420270109/100000000000000000000)
  directionLo := (23247014150427004819/4000000000000000000)
  directionHi := (145293838440168780119/25000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree137.table
  base := (22110536801925096493291499251147250292977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-31588135233422723882959481904895000000000000)
      constant := (983420258082383386924683848977915585651085513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree137.table
  base := (88442147185558904825925083198763899366747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-281840824813595446620607259691567820000000000000)
      constant := (8855223025248021312251080105202543952116866304387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23247014150427004819/4000000000000000000)
  centralHi := (145293838440168780119/25000000000000000000)
  directionLo := (145827028629934692739/25000000000000000000)
  directionHi := (583308114519738770957/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree138.table
  base := (45299006114699581907741229132716756912147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-63656438734674079464870288744910000000000000)
      constant := (1997453449777874073267884900735229240212729243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree138.table
  base := (90598012210184243131110404175172934364747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-283982121081381117075266018200766780000000000000)
      constant := (8992949121615617671657105851142932569444053062387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145827028629934692739/25000000000000000000)
  centralHi := (583308114519738770957/100000000000000000000)
  directionLo := (585433105581072762651/100000000000000000000)
  directionHi := (146358276395268190663/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree139.table
  base := (23194273855963172744161598147735083874877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-32068303501251355581910806840015000000000000)
      constant := (1014151447041509063336524876763654329824706613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree139.table
  base := (18555419081435676485662475936754849112861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-286123417349166787529924776709965740000000000000)
      constant := (9131738506404377788363863006903966185270171600905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585433105581072762651/100000000000000000000)
  centralHi := (146358276395268190663/25000000000000000000)
  directionLo := (1468876028116452159/250000000000000000)
  directionHi := (587550411246580863601/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree140.table
  base := (94979396779022055124840440356338013625467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-129233550540662685725545877230300000000000000)
      constant := (4118777698143916597147466547337826740653264323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree140.table
  base := (47489698382276591022485430227136536900393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-144132356808476228992291767609582350000000000000)
      constant := (4635795589789024037206254150657105871107753379553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1468876028116452159/250000000000000000)
  centralHi := (587550411246580863601/100000000000000000000)
  directionLo := (73707514288079151429/12500000000000000000)
  directionHi := (589660114304633211433/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree141.table
  base := (3037653633847213254414246783414714803097/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-16274235884539993640431065887567500000000000)
      constant := (522677828684154982796152725733756478261759172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree141.table
  base := (48602458135278160427826237832043089578771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 321715000000000000000000000000000000000000000
      center := (1794130)
      previous := (1551706)
      next := (0)
      square := (24559194639823250719892766534520000000000000)
      linear := (-3089425637071682217438747805620890000000000000)
      constant := (100133054692564766900945479186896893512766862453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73707514288079151429/12500000000000000000)
  centralHi := (589660114304633211433/100000000000000000000)
  directionLo := (591762296067838300009/100000000000000000000)
  directionHi := (59176229606783830001/10000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree142.table
  base := (19890730784910886539457245846968262581169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-131154223611977212521351176970780000000000000)
      constant := (4244540582138174159076502938296777757368101805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree142.table
  base := (19890730782732310997384944930626959251113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-292547306152523798893901052237562620000000000000)
      constant := (9554486390938641075044194666337596873187175483365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591762296067838300009/100000000000000000000)
  centralHi := (59176229606783830001/10000000000000000000)
  directionLo := (148464259102402892147/25000000000000000000)
  directionHi := (593857036409611568589/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree143.table
  base := (10172560969201052437911001191910067485419/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-66057280073817237959626913420510000000000000)
      constant := (2154065778061595900669394206941714411937693055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree143.table
  base := (101725609682559817528521346776099048480593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-294688602420309469348559810746761580000000000000)
      constant := (9697528929056507046744725855213093000590179383753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148464259102402892147/25000000000000000000)
  centralHi := (593857036409611568589/100000000000000000000)
  directionLo := (297972206899793561989/50000000000000000000)
  directionHi := (595944413799587123979/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree144.table
  base := (10402078357435013194482909464814839184169/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-66537448341645869658578238355630000000000000)
      constant := (2186097775706528616500959832315617574215636805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree144.table
  base := (20804156713230211515480994026237408881051/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-296829898688095139803218569255960540000000000000)
      constant := (9841634755421118106753524330041777575913864155855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297972206899793561989/50000000000000000000)
  centralHi := (595944413799587123979/100000000000000000000)
  directionLo := (299012252668958507351/50000000000000000000)
  directionHi := (598024505337917014703/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree145.table
  base := (21267835112129918800221753998498433238919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-134035233218949002715059126581500000000000000)
      constant := (4436732567992815961618421476069221775520400555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree145.table
  base := (53169587776768364868801371861142474654247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-149485597477940405128938663882579750000000000000)
      constant := (4993401934999757867534587638348215916593876091887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299012252668958507351/50000000000000000000)
  centralHi := (598024505337917014703/100000000000000000000)
  directionLo := (600097386788500474553/100000000000000000000)
  directionHi := (300048693394250237277/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree146.table
  base := (108680785640183119942330964343122249049277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-134995569754606266112961776451740000000000000)
      constant := (4501742605847784379849202705426654358948460213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree146.table
  base := (108680785634012857094311550449230259812803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-301112491223666480712536086274358460000000000000)
      constant := (10133036272759329810320107377888995242535353621163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600097386788500474553/100000000000000000000)
  centralHi := (300048693394250237277/50000000000000000000)
  directionLo := (150540783152795913661/25000000000000000000)
  directionHi := (120432626522236730929/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree147.table
  base := (55522806901207963350301861722922817927603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-67977953145131764755432213160990000000000000)
      constant := (2283612832481770184837159633664771337742888507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree147.table
  base := (55522806898531800469696080758203868814701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-151626893745726075583597422391778710000000000000)
      constant := (5140165981834379581918211960447421526963782402821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150540783152795913661/25000000000000000000)
  centralHi := (120432626522236730929/20000000000000000000)
  directionLo := (302110907996484281063/50000000000000000000)
  directionHi := (604221815992968562127/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree148.table
  base := (22686732007399576192788414204387481264513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (2080)
      previous := (1768)
      next := (0)
      square := (28245192225213629350077937360000000000000)
      linear := (-3700438995295156565101812870060000000000000)
      constant := (125221128252051745907828749439251684033934905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree148.table
  base := (22686732006471055874802545975400725998903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 817330000000000000000000000000000000000000000
      center := (4558060)
      previous := (3942172)
      next := (0)
      square := (62393629625496907234322163628240000000000000)
      linear := (-8253921182682103287077124413317740000000000000)
      constant := (281856511964771715977852638961916697690341694495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302110907996484281063/50000000000000000000)
  centralHi := (604221815992968562127/100000000000000000000)
  directionLo := (303136754439134107273/50000000000000000000)
  directionHi := (606273508878268214547/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree149.table
  base := (115844924333757589251876034503441174514763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-137876579361578056306669726062460000000000000)
      constant := (4699610846920982428920472698749430967910710547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree149.table
  base := (28961231082432696137078326374369797982567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-76884095006755873019128090450488835000000000000)
      constant := (2644528302452999117301113054505461075344838498607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303136754439134107273/50000000000000000000)
  centralHi := (606273508878268214547/100000000000000000000)
  directionLo := (608318281998243396091/100000000000000000000)
  directionHi := (152079570499560849023/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree150.table
  base := (118279406682696885781781092187263604443717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-138836915897235319704572375932700000000000000)
      constant := (4766512969735056371710333205609363874483448573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree150.table
  base := (29569851669801088721459037682709040433027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-77419419073702290632792780077788575000000000000)
      constant := (2682149691246222486655944675039211121063366044267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608318281998243396091/100000000000000000000)
  centralHi := (152079570499560849023/25000000000000000000)
  directionLo := (610356204899254860803/100000000000000000000)
  directionHi := (152589051224813715201/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree151.table
  base := (120737107073985674578453021438027031057423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-139797252432892583102475025802940000000000000)
      constant := (4833888113754679025569190669044279005517612087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree151.table
  base := (120737107070956664327007051146807811368921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-311818972562594832985829878820353260000000000000)
      constant := (10880147608185539093295921455078845715324792743441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610356204899254860803/100000000000000000000)
  centralHi := (152589051224813715201/25000000000000000000)
  directionLo := (306193672985231681793/50000000000000000000)
  directionHi := (612387345970463363587/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree152.table
  base := (61609012748978543957243964691453632403761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-70378794484274923250188837836590000000000000)
      constant := (2450868139483308224289114579855640022760748809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree152.table
  base := (6160901274766509776796090397898118978627/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-78490067207595125860122159332388055000000000000)
      constant := (2758189934846184602059377135311650267318822309335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306193672985231681793/50000000000000000000)
  centralHi := (612387345970463363587/100000000000000000000)
  directionLo := (122882354494121701643/20000000000000000000)
  directionHi := (76801471558826063527/12500000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree153.table
  base := (62861080972551464020583387818100049585353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-70858962752103554949140162771710000000000000)
      constant := (2485028732678925959009726155661168967882348257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree153.table
  base := (502888647771299473022157923735744426003/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-158050782549083086947573697919375590000000000000)
      constant := (5593217579276879249620768526724861331163577295375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122882354494121701643/20000000000000000000)
  centralHi := (76801471558826063527/12500000000000000000)
  directionLo := (616429550553996078469/100000000000000000000)
  directionHi := (61642955055399607847/10000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree154.table
  base := (128249516406069363383353611011521292004621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-142678262039864373296182975413660000000000000)
      constant := (5038851672915580038466499009441292648754326149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree154.table
  base := (128249516404093897660612431970180120493659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-318242861365951844349806154347950140000000000000)
      constant := (11341173865664333558035494279095844056167404548739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (616429550553996078469/100000000000000000000)
  centralHi := (61642955055399607847/10000000000000000000)
  directionLo := (618440745295722260193/100000000000000000000)
  directionHi := (309220372647861130097/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree155.table
  base := (130800088871652854017598773111764538905399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-143638598575521636694085625283900000000000000)
      constant := (5108118901627201163764166666246505653761491231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree155.table
  base := (130800088869939860724968883035677626304467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-320384157633737514804464912857149100000000000000)
      constant := (11496975860688649464500050594634028708937491048507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618440745295722260193/100000000000000000000)
  centralHi := (309220372647861130097/50000000000000000000)
  directionLo := (620445420716161964961/100000000000000000000)
  directionHi := (310222710358080982481/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree156.table
  base := (26674775866559256881594727170474059166173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-144598935111178900091988275154140000000000000)
      constant := (5177859151480316102743768992628214934992454185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree156.table
  base := (133373879331310951358711190421893431700853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-322525453901523185259123671366348060000000000000)
      constant := (11653841143599332461750818647874777466568615275213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620445420716161964961/100000000000000000000)
  centralHi := (310222710358080982481/50000000000000000000)
  directionLo := (311221819902373663357/50000000000000000000)
  directionHi := (124488727960949465343/20000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree157.table
  base := (135970887780585284106237670284715816321751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-145559271646836163489890925024380000000000000)
      constant := (5248072422462721082261664704455755952544477119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree157.table
  base := (135970887779297407440587724850108719254233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-324666750169308855713782429875547020000000000000)
      constant := (11811769714369438351051916840432101900179830354193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311221819902373663357/50000000000000000000)
  centralHi := (124488727960949465343/20000000000000000000)
  directionLo := (624435464543061358117/100000000000000000000)
  directionHi := (312217732271530679059/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree158.table
  base := (69295557103122359744804237756180935091859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-73259804091246713443896787447310000000000000)
      constant := (2659379357281201472194132347450951700140754971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree158.table
  base := (138591114205128094922121609823130233284943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-326808046437094526168441188384745980000000000000)
      constant := (11970761572972442161733531232076433444211895110103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624435464543061358117/100000000000000000000)
  centralHi := (312217732271530679059/50000000000000000000)
  directionLo := (626420955927270720531/100000000000000000000)
  directionHi := (156605238981817680133/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree159.table
  base := (35308639650283835415147048234541495532401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3422500000000000000000000000000000000000000
      center := (19240)
      previous := (16354)
      next := (0)
      square := (261268028083226071488220920580000000000000)
      linear := (-36869986179537672571424056191215000000000000)
      constant := (1347479506941883639345723598886792307383856969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree159.table
  base := (70617279300083617978437481024428725461069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-164474671352440098311549973446972470000000000000)
      constant := (6065408359691114128329457122374290886670053445349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (626420955927270720531/100000000000000000000)
  centralHi := (156605238981817680133/25000000000000000000)
  directionLo := (628400173989920577541/100000000000000000000)
  directionHi := (314200086994960288771/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree160.table
  base := (5756048838270023096480991620312502897269/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-148440281253807953683598874635100000000000000)
      constant := (5461550362066470422524962674509195411659031525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree160.table
  base := (143901220955911269548225756782784520710383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-331090638972665867077758705403143900000000000000)
      constant := (12291935153573080838443400284356167107555204148343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628400173989920577541/100000000000000000000)
  centralHi := (314200086994960288771/50000000000000000000)
  directionLo := (315186588910556782209/50000000000000000000)
  directionHi := (630373177821113564419/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree161.table
  base := (5863644050588538068160194478982595422119/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-149400617789465217081501524505340000000000000)
      constant := (5533655717447742460984828078636199328322022775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree161.table
  base := (45809719144995573295241206768831998277/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-83307983810112884383104365978085715000000000000)
      constant := (3113529218879918706416862495742618650669151613600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315186588910556782209/50000000000000000000)
  centralHi := (630373177821113564419/100000000000000000000)
  directionLo := (316170012794547006089/50000000000000000000)
  directionHi := (632340025589094012179/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree162.table
  base := (149304199516773631439305118595439951068811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-150360954325122480479404174375580000000000000)
      constant := (5606234093900055966752391925639037293013202259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree162.table
  base := (149304199516142865971951834307488926987113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-335373231508237207987076222421541820000000000000)
      constant := (12617361885197067071832127616918599341369195152673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316170012794547006089/50000000000000000000)
  centralHi := (632340025589094012179/100000000000000000000)
  directionLo := (63430077456025771277/10000000000000000000)
  directionHi := (634300774560257712771/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree163.table
  base := (15204051570480458148861587375359937310211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-75660645430389871938653412122910000000000000)
      constant := (2839642745706142856617814627269628770888394295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree163.table
  base := (152040515704257796695825585473119558867787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-337514527776022878441734980930740780000000000000)
      constant := (12781670182580687902851775149553675963482810890227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63430077456025771277/10000000000000000000)
  centralHi := (634300774560257712771/100000000000000000000)
  directionLo := (636255481118606699191/100000000000000000000)
  directionHi := (79531935139825837399/12500000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree164.table
  base := (154800049820800824929433120873460945666959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-152281627396437007275209474116060000000000000)
      constant := (5752809909973472202527632080334888034618066871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree164.table
  base := (967500311377042858068630919532874241449/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7560302500000000000000000000000000000000000000
      center := (42162055)
      previous := (36465091)
      next := (0)
      square := (577141074035846391917480013561220000000000000)
      linear := (-84913956010952137224098434859984935000000000000)
      constant := (3236760441911583237881961427468730977356999653160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636255481118606699191/100000000000000000000)
  centralHi := (79531935139825837399/12500000000000000000)
  directionLo := (319102100392333869463/50000000000000000000)
  directionHi := (638204200784667738927/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree165.table
  base := (78791400928437650171983560884991614614143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-76620981966047135336556061993150000000000000)
      constant := (2913403674786409023773723125725303520406761767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree165.table
  base := (157582801856464467747138603881687514610583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-341797120311594219351052497949138700000000000000)
      constant := (13113476640370155269754073404369341478371670872543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319102100392333869463/50000000000000000000)
  centralHi := (638204200784667738927/100000000000000000000)
  directionLo := (80018373529236562387/12500000000000000000)
  directionHi := (640146988233892499097/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree166.table
  base := (20048596475657101223673075065788980924303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1711250000000000000000000000000000000000000
      center := (9620)
      previous := (8177)
      next := (0)
      square := (130634014041613035744110460290000000000000)
      linear := (-19275287558468941758876846732067500000000000)
      constant := (737659726274960559788916626644530114885370807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree166.table
  base := (641555087219602861254616184958661622171/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-171969208289689944902855628229168830000000000000)
      constant := (6640487400364328850606533204157500982937673336375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80018373529236562387/12500000000000000000)
  centralHi := (640146988233892499097/100000000000000000000)
  directionLo := (321041948657278317661/50000000000000000000)
  directionHi := (642083897314556635323/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree167.table
  base := (81608979829143775861760571912996989060891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6845000000000000000000000000000000000000000
      center := (38480)
      previous := (32708)
      next := (0)
      square := (522536056166452142976441841160000000000000)
      linear := (-77581318501704398734458711863390000000000000)
      constant := (2988110645921793982254034641810782878024359779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree167.table
  base := (81608979828989456680539617481055373369927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-173039856423582780130185007483768310000000000000)
      constant := (6724768124349342749539145843923109641770837009167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321041948657278317661/50000000000000000000)
  centralHi := (642083897314556635323/100000000000000000000)
  directionLo := (644014981065174381753/100000000000000000000)
  directionHi := (322007490532587190877/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree168.table
  base := (166070365408420733754075679235751144962259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-156122973539066060866820073597020000000000000)
      constant := (6051637794494196947352594894685423317453332571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree168.table
  base := (16607036540815323664570019309248323284819/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15120605000000000000000000000000000000000000000
      center := (84324110)
      previous := (72930182)
      next := (0)
      square := (1154282148071692783834960027122440000000000000)
      linear := (-174110504557475615357514386738367790000000000000)
      constant := (6809580492128709587383951843627601903302050595495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell028.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (644014981065174381753/100000000000000000000)
  centralHi := (322007490532587190877/50000000000000000000)
  directionLo := (645940291731444575433/100000000000000000000)
  directionHi := (322970145865722287717/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 17
  qDenominator := 37
  table := BinomialMassData.Q17_37.Degree169.table
  base := (6757839561928730423626323870493679900627/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (76960)
      previous := (65416)
      next := (0)
      square := (1045072112332904285952883682320000000000000)
      linear := (-157083310074723324264722723467260000000000000)
      constant := (6127527318141328674392365785767066194598959075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q17_37.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree169.table
  base := (168945989047986428806411238391100778567693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30241210000000000000000000000000000000000000000
      center := (168648220)
      previous := (145860364)
      next := (0)
      square := (2308564296143385567669920054244880000000000000)
      linear := (-350362305382736901169687531985934540000000000000)
      constant := (13789849007382367565137899129661605907582910322853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell028.Kernel169
