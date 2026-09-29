import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell143.Parameters
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch000_049
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch050_099
import ForestUnimodality.BinomialMassData.Q47837_90312.Batch100_149
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95699_180624.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree000.table
  base := (5421906950835899057338451681/100000000000000000000000000)
  polynomial :=
    { denominator := 301040000000000000000000000000000000000000000
      center := (1865643)
      previous := (0)
      next := (1656525)
      square := (43491626071693075306079379408000000000000000)
      linear := (-199652699531917568469552294684000000000000000)
      constant := (16322108684796390522211674940482400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree000.table
  base := (5421906950835899057338451681/100000000000000000000000000)
  polynomial :=
    { denominator := 602080000000000000000000000000000000000000000
      center := (3732261)
      previous := (0)
      next := (3312075)
      square := (86983252143386150612158758816000000000000000)
      linear := (-399305399063835136939104589368000000000000000)
      constant := (32644217369592781044423349880964800000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree001.table
  base := (162530943061242173973473832343776036247453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-2774006554113712841307005672872800000000000000000)
      constant := (111801950154198336372372429390030725777874894378736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree001.table
  base := (325005385497359320764442739697046934750199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-5548284930890373764334674341866900000000000000000)
      constant := (223566265419328951962783321193901287180749949934288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1996438853421416081/4000000000000000000)
  directionHi := (24955485667767701013/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree002.table
  base := (101895638063488290654821535609902315509531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-3294133783211608252161235491057924000000000000000)
      constant := (72195958602823178306829248766975873333101443395472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree002.table
  base := (101864180584719108527767189565389941859201/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-6588811211749112667763796974358448000000000000000)
      constant := (144350978484169785992067794908682967752140195037024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1996438853421416081/4000000000000000000)
  centralHi := (24955485667767701013/50000000000000000000)
  directionLo := (35292386286964477181/50000000000000000000)
  directionHi := (70584772573928954363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree003.table
  base := (67242700453326956255485852707802637045691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-1271420337436501221005155103081016000000000000000)
      constant := (16841792462060124133312482951681030597402324508464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree003.table
  base := (26886348055639973967786935126895855234809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-2543112497535950523730973202283332000000000000000)
      constant := (33672483340118272657305679480193523816954409817680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35292386286964477181/50000000000000000000)
  centralHi := (70584772573928954363/100000000000000000000)
  directionLo := (43224169104130589573/50000000000000000000)
  directionHi := (86448338208261179147/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree004.table
  base := (93559124430712737436430452373708033981783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-4334388241407399073869695127428172000000000000000)
      constant := (38774938214249880890006002661558912028154964831848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree004.table
  base := (18703440823198081684914262540112730229167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-8669863773466590474622042239341544000000000000000)
      constant := (77526183339104508583503661839089621383139227813520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43224169104130589573/50000000000000000000)
  centralHi := (86448338208261179147/100000000000000000000)
  directionLo := (99821942671070804051/100000000000000000000)
  directionHi := (24955485667767701013/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree005.table
  base := (68306680112057759049492615965729654607411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-4854515470505294484723924945613296000000000000000)
      constant := (32626661835483960773616897621974071571261641899016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree005.table
  base := (68274712758762284146715534532913266468941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-9710390054325329378051164871833092000000000000000)
      constant := (65238315400998356075990367973036433071027414929392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99821942671070804051/100000000000000000000)
  centralHi := (24955485667767701013/25000000000000000000)
  directionLo := (11160432472930062383/10000000000000000000)
  directionHi := (111604324729300623831/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree006.table
  base := (10371504882294646095048758786848053475357/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-1791547566534396631859384921266140000000000000000)
      constant := (9915211622196979191243299540102682581283698213320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree006.table
  base := (51832912201485897623756427875491129646857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-3583638778394689427160095834774880000000000000000)
      constant := (19827822858491384513857889230943150160806487021328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11160432472930062383/10000000000000000000)
  centralHi := (111604324729300623831/100000000000000000000)
  directionLo := (122256412338739186949/100000000000000000000)
  directionHi := (2445128246774783739/2000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree007.table
  base := (40475755818488478757982537330727914196777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-5894769928701085306432384581983544000000000000000)
      constant := (28862233385435931324029916920821601543052677807512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree007.table
  base := (40456249391192957665240139515326673048879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-11791442616042807184909410136816188000000000000000)
      constant := (57722631860684047145147749085019574592833851226448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122256412338739186949/100000000000000000000)
  centralHi := (2445128246774783739/2000000000000000000)
  directionLo := (132052017847499989907/100000000000000000000)
  directionHi := (33013004461874997477/25000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree008.table
  base := (32112968412308621109890510863024720484759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-6414897157798980717286614400168668000000000000000)
      constant := (29280318815561594313860182066656457437806784742504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree008.table
  base := (32096917704544375132758627141714249305737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-12831968896901546088338532769307736000000000000000)
      constant := (58563935439069596254428343185827166554113692298544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132052017847499989907/100000000000000000000)
  centralHi := (33013004461874997477/25000000000000000000)
  directionLo := (35292386286964477181/25000000000000000000)
  directionHi := (5646781805914316349/4000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree009.table
  base := (1281596809973557961836590017904762085097/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-2311674795632292042713614739451264000000000000000)
      constant := (10204470554253667213004826521460121374762544222880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree009.table
  base := (25618228324495750415753336809065914199827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-4624165059253428330589218467266428000000000000000)
      constant := (20411595144880793159313790399508468610344801452208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35292386286964477181/25000000000000000000)
  centralHi := (5646781805914316349/4000000000000000000)
  directionLo := (149732914006606206077/100000000000000000000)
  directionHi := (74866457003303103039/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree010.table
  base := (20389597646028294771826374557764216771383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-7455151615994771538995074036538916000000000000000)
      constant := (32642971287079751810290092337008257719250023449448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree010.table
  base := (10188759741165597676795056720896245506063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-14913021458619023895196778034290832000000000000000)
      constant := (65298372283169314127382251537071867611808890046112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149732914006606206077/100000000000000000000)
  centralHi := (74866457003303103039/50000000000000000000)
  directionLo := (157832349651667941977/100000000000000000000)
  directionHi := (78916174825833970989/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree011.table
  base := (16012645336832460626844476896626706117651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-7975278845092666949849303854724040000000000000000)
      constant := (35242131382419219789856925647860294274942529032456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree011.table
  base := (4000438740474258600362420390158594650559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-15953547739477762798625900666782380000000000000000)
      constant := (70501147703185284569832199469760698439446985818432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157832349651667941977/100000000000000000000)
  centralHi := (78916174825833970989/50000000000000000000)
  directionLo := (82767982421077236981/50000000000000000000)
  directionHi := (165535964842154473963/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree012.table
  base := (6138232108199541703616118350117109915577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-2831802024730187453567844557636388000000000000000)
      constant := (12778185952428287703293367925477481139138336840208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree012.table
  base := (6133246622487452724905581187919581801429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-5664691340112167234018341099757976000000000000000)
      constant := (25563520487639346219779543889134745174961890608032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82767982421077236981/50000000000000000000)
  centralHi := (165535964842154473963/100000000000000000000)
  directionLo := (43224169104130589573/25000000000000000000)
  directionHi := (172896676416522358293/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree013.table
  base := (2259897854224871536047217787613176729291/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-9015533303288457771557763491094288000000000000000)
      constant := (41872175396900392276168583233834918904908269777184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree013.table
  base := (2257594447318375042204936402431969683167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-18034600301195240605484145931765476000000000000000)
      constant := (83770535201018748883172658898248665854572065642816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43224169104130589573/25000000000000000000)
  centralHi := (172896676416522358293/100000000000000000000)
  directionLo := (17995656635848627789/10000000000000000000)
  directionHi := (179956566358486277891/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree014.table
  base := (6208049717352665560411506555840984375679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-9535660532386353182411993309279412000000000000000)
      constant := (45823046401316014836014462684312656621263379114024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree014.table
  base := (3099747073924025352916008001752990196907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-19075126582053979508913268564257024000000000000000)
      constant := (91677236384354001811292784035811934694580454139168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17995656635848627789/10000000000000000000)
  centralHi := (179956566358486277891/100000000000000000000)
  directionLo := (37349950915733697513/20000000000000000000)
  directionHi := (93374877289334243783/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree015.table
  base := (3715788021418007323720581337749553679309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-3351929253828082864422074375821512000000000000000)
      constant := (16721574599349363219079369533558549328188697945768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree015.table
  base := (741565395919733030261885987934737485689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-6705217620970906137447463732249524000000000000000)
      constant := (33455265056789525302766893192495321876439305715280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37349950915733697513/20000000000000000000)
  centralHi := (93374877289334243783/50000000000000000000)
  directionLo := (193304360775564368249/100000000000000000000)
  directionHi := (773217443102257473/400000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree016.table
  base := (75691579498745025531121447864273671271/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-10575914990582144004120452945649660000000000000000)
      constant := (54880563813112326450401527656035034038774946303520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree016.table
  base := (23537830293134526585311563299694125057/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-21156179143771457315771513829240120000000000000000)
      constant := (109802937328464954458914350407745581762398990232576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193304360775564368249/100000000000000000000)
  centralHi := (773217443102257473/400000000000000000)
  directionLo := (99821942671070804051/50000000000000000000)
  directionHi := (199643885342141608103/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree017.table
  base := (-435838148136727577653821426547776877453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-11096042219680039414974682763834784000000000000000)
      constant := (59957646061082361484299560889134426178183357530632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree017.table
  base := (-221365841476605482611334899947675945229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-22196705424630196219200636461731668000000000000000)
      constant := (119962829063343167690095203483542958600998971164704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99821942671070804051/50000000000000000000)
  centralHi := (199643885342141608103/100000000000000000000)
  directionLo := (51447051673396954119/25000000000000000000)
  directionHi := (205788206693587816477/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree018.table
  base := (-2163819590353896931084337985009032453853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-3872056482925978275276304194006636000000000000000)
      constant := (21795190619488699293661875988438373071415654550744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree018.table
  base := (-1085112397210936932068186648067078789227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-7745743901829645040876586364741072000000000000000)
      constant := (43608225488883787636314931714646419012263369620384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51447051673396954119/25000000000000000000)
  centralHi := (205788206693587816477/100000000000000000000)
  directionLo := (105877158860893431543/50000000000000000000)
  directionHi := (211754317721786863087/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree019.table
  base := (-1847700989990829639565374551197576366153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-12136296677875830236683142400205032000000000000000)
      constant := (71155746806245576015429674398092941730713646726864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree019.table
  base := (-3701345071707831036869576450273924252157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-24277757986347674026058881726714764000000000000000)
      constant := (142371292349340274093225356225047184667220396742416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105877158860893431543/50000000000000000000)
  centralHi := (211754317721786863087/100000000000000000000)
  directionLo := (54389220056388526099/25000000000000000000)
  directionHi := (217556880225554104397/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree020.table
  base := (-5051879989366433369757611672948796423997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-12656423906973725647537372218390156000000000000000)
      constant := (77260934036599397903248983428285705542950563788168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree020.table
  base := (-9877707301570038719600642026912118967/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-25318284267206412929488004359206312000000000000000)
      constant := (154588203688592487755187211037497147318732994404352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54389220056388526099/25000000000000000000)
  centralHi := (217556880225554104397/100000000000000000000)
  directionLo := (223208649458601247661/100000000000000000000)
  directionHi := (111604324729300623831/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree021.table
  base := (-3125707193822094292139817243930311961319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-4392183712023873686130534012191760000000000000000)
      constant := (27898320573361438698135251269278773184480023953424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree021.table
  base := (-3128254130508157830398545418656510423089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-8786270182688383944305708997232620000000000000000)
      constant := (55821022389050960777973067362569314277681544254688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223208649458601247661/100000000000000000000)
  centralHi := (111604324729300623831/50000000000000000000)
  directionLo := (228720804153862154969/100000000000000000000)
  directionHi := (22872080415386215497/10000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree022.table
  base := (-7309626841326285204617519503848723863611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-13696678365169516469245831854760404000000000000000)
      constant := (90452520926191630540614750713406572071766446953784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree022.table
  base := (-7314332746252050568887132815365233391747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-27399336828923890736346249624189408000000000000000)
      constant := (180985265168558904640490706258227457425524125188336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228720804153862154969/100000000000000000000)
  centralHi := (22872080415386215497/10000000000000000000)
  directionLo := (117051603270145347629/50000000000000000000)
  directionHi := (234103206540290695259/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree023.table
  base := (-8240033225826759936874170148325038406349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-14216805594267411880100061672945528000000000000000)
      constant := (97529018365000244328341083490848487091630579688456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree023.table
  base := (-4122187529755054236783759813407599066417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-28439863109782629639775372256680956000000000000000)
      constant := (195145611391650677183007292683480878533188133330592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117051603270145347629/50000000000000000000)
  centralHi := (234103206540290695259/100000000000000000000)
  directionLo := (119682304845059113597/50000000000000000000)
  directionHi := (47872921938023645439/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree024.table
  base := (-905437431686311752314916191699385484969/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-4912310941121769096984763830376884000000000000000)
      constant := (34973488001223244778610132815941236346935360019120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree024.table
  base := (-452918771954934121526251695288689292033/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-9826796463547122847734831629724168000000000000000)
      constant := (69978708712006024716439233737178333867623157255360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119682304845059113597/50000000000000000000)
  centralHi := (47872921938023645439/20000000000000000000)
  directionLo := (244512824677478373899/100000000000000000000)
  directionHi := (2445128246774783739/1000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree025.table
  base := (-9762877826374333045402645472039508131481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-15257060052463202701808521309315776000000000000000)
      constant := (112623382015091159646746425552924427714352515673064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree025.table
  base := (-9766560915859780598244626355414529317513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-30520915671500107446633617521664052000000000000000)
      constant := (225349858210376725243892698918536735715810940494544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244512824677478373899/100000000000000000000)
  centralHi := (2445128246774783739/1000000000000000000)
  directionLo := (15597178542354813133/6250000000000000000)
  directionHi := (249554856677677010129/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree026.table
  base := (-10374471996250946559543260757608168724561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-15777187281561098112662751127500900000000000000000)
      constant := (120634738189327490020458705842088395081912842940584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree026.table
  base := (-10377858920231126778404111907757083807953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-31561441952358846350062740154155600000000000000000)
      constant := (241380739746387402642392429341056233051946654845264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15597178542354813133/6250000000000000000)
  centralHi := (249554856677677010129/100000000000000000000)
  directionLo := (254497016782265151891/100000000000000000000)
  directionHi := (63624254195566287973/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree027.table
  base := (-10896963269731851491682518650266209532653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-5432438170219664507838993648562008000000000000000)
      constant := (42983959851015162046028589050245059874225780013144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree027.table
  base := (-218001499586335245949122976633584600513/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-10867322744405861751163954262215716000000000000000)
      constant := (86007821806689865222690103174312922159750746642400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254497016782265151891/100000000000000000000)
  centralHi := (63624254195566287973/25000000000000000000)
  directionLo := (259345014624783537439/100000000000000000000)
  directionHi := (1620906341404897109/625000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree028.table
  base := (-11337186174008657605674975443137162183161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-16817441739756888934371210763871148000000000000000)
      constant := (137572483432803509048310074874129355439344750858984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree028.table
  base := (-11340042628330172922366202920032059616581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-33642494514076324156920985419138696000000000000000)
      constant := (275273390558775764663038710050240794419734616214928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259345014624783537439/100000000000000000000)
  centralHi := (1620906341404897109/625000000000000000)
  directionLo := (132052017847499989907/50000000000000000000)
  directionHi := (52820807138999995963/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree029.table
  base := (-731320686257110140358401742505801317199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-17337568968854784345225440582056272000000000000000)
      constant := (146494514070597369530270384195673938779327188493696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree029.table
  base := (-11703751097917248140030599789372960973393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-34683020794935063060350108051630244000000000000000)
      constant := (293126444353635872461388418624907189617144829595984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132052017847499989907/50000000000000000000)
  centralHi := (52820807138999995963/20000000000000000000)
  directionLo := (268778806326024262339/100000000000000000000)
  directionHi := (13438940316301213117/5000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree030.table
  base := (-2398810629991669556391404690598352353979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-5952565399317559918693223466747132000000000000000)
      constant := (51905395142978339285185842413920494781844381501960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree030.table
  base := (-2999113696303285988012226812696732690803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-11907849025264600654593076894707264000000000000000)
      constant := (103859685151127142223855585340468539338425905554752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268778806326024262339/100000000000000000000)
  centralHi := (13438940316301213117/5000000000000000000)
  directionLo := (273373648674664867699/100000000000000000000)
  directionHi := (2733736486746648677/1000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree031.table
  base := (-6110283797671412414562158156509579120143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-18377823427050575166933900218426520000000000000000)
      constant := (165235929157472120218378687095669585407915383159984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree031.table
  base := (-3055691883203662956744608093411168086957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-36764073356652540867208353316613340000000000000000)
      constant := (330628087884048748923052298833951253218046179379264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273373648674664867699/100000000000000000000)
  centralHi := (2733736486746648677/1000000000000000000)
  directionLo := (5557850550324495119/2000000000000000000)
  directionHi := (277892527516224755951/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree032.table
  base := (-6192365059289961527544578665614767911741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-18897950656148470577788130036611644000000000000000)
      constant := (175052366915900384387979218106215939078750577077008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree032.table
  base := (-6193372042682464474426450186139178083309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-37804599637511279770637475949104888000000000000000)
      constant := (350270785683906689595709927827287866958647854154784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5557850550324495119/2000000000000000000)
  centralHi := (277892527516224755951/100000000000000000000)
  directionLo := (35292386286964477181/12500000000000000000)
  directionHi := (282339090295715817449/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree033.table
  base := (-2498021589107726443102476766025679109597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-6472692628415455329547453284932256000000000000000)
      constant := (61721428801237274920390964119121365268733478324280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree033.table
  base := (-12491950634938037208993793717488804308039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-12948375306123339558022199527198812000000000000000)
      constant := (123501574984865800066152065131931917781243835222544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35292386286964477181/12500000000000000000)
  centralHi := (282339090295715817449/100000000000000000000)
  directionLo := (143358350793273467953/50000000000000000000)
  directionHi := (286716701586546935907/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree034.table
  base := (-12539840924586736479963662026525463869001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-19938205114344261399496589672981892000000000000000)
      constant := (195570620562101908586040562707427262771477247491944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree034.table
  base := (-2508305205840000552521511446028970052707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-39885652199228757577495721214087984000000000000000)
      constant := (391327772258676903807316214088946396737855193404080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143358350793273467953/50000000000000000000)
  centralHi := (286716701586546935907/100000000000000000000)
  directionLo := (291028472882509629517/100000000000000000000)
  directionHi := (145514236441254814759/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree035.table
  base := (-39177170957256476869044845107274611517/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-20458332343442156810350819491167016000000000000000)
      constant := (206270429501153988196754854893129106843196290255360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree035.table
  base := (-3134558739437531392159165247547544513331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-40926178480087496480924843846579532000000000000000)
      constant := (412738048469491186196674698901486385482992375115712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291028472882509629517/100000000000000000000)
  centralHi := (145514236441254814759/50000000000000000000)
  directionLo := (5905545769460508697/2000000000000000000)
  directionHi := (295277288473025434851/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree036.table
  base := (-12483107014066679603370384213802895292173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-6992819857513350740401683103117380000000000000000)
      constant := (72420961591695632017997461923923796959788207542104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree036.table
  base := (-12484514227094414298052266922959392316979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-13988901586982078461451322159690360000000000000000)
      constant := (144911299106208956338767877192646252394468412648784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5905545769460508697/2000000000000000000)
  centralHi := (295277288473025434851/100000000000000000000)
  directionLo := (149732914006606206077/50000000000000000000)
  directionHi := (59893165602642482431/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree037.table
  base := (-12381227948639735082018220010172275490217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-21498586801637947632059279127537264000000000000000)
      constant := (228547255684917433924265666582533801388655266399848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree037.table
  base := (-1547814133523509299909308078907172799621/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-43007231041804974287783089111562628000000000000000)
      constant := (457313857999353756718394248033302226697542785555584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149732914006606206077/50000000000000000000)
  centralHi := (59893165602642482431/20000000000000000000)
  directionLo := (303596586290583235279/100000000000000000000)
  directionHi := (3794957328632290441/1250000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree038.table
  base := (-12232955133292161115915903089475405198769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-22018714030735843042913508945722388000000000000000)
      constant := (240122897334663248541529298324853913385006856832936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree038.table
  base := (-12234128282789140726038396925944005692449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-44047757322663713191212211744054176000000000000000)
      constant := (480476641278066092312381112902413084453182086533712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303596586290583235279/100000000000000000000)
  centralHi := (3794957328632290441/1250000000000000000)
  directionLo := (307671890602557628247/100000000000000000000)
  directionHi := (38458986325319703531/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree039.table
  base := (-3009991097369374468472378209143693596967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-7512947086611246151255912921302504000000000000000)
      constant := (83996413402121478999750167140667357758247340562464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree039.table
  base := (-3010258729899458019053896163980176693383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-15029427867840817364880444792181908000000000000000)
      constant := (168073702881358438676517340853637623438797474449472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307671890602557628247/100000000000000000000)
  centralHi := (38458986325319703531/12500000000000000000)
  directionLo := (15584695804426920667/5000000000000000000)
  directionHi := (311693916088538413341/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree040.table
  base := (-11803736536878206113479745104257863956637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-23058968488931633864621968582092636000000000000000)
      constant := (264145781052253907201525813210304604643080273800328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree040.table
  base := (-11804713073847555740009777697446846306331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-46128809884381190998070457009037272000000000000000)
      constant := (528546254094246653069501354160086625813695708962928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15584695804426920667/5000000000000000000)
  centralHi := (311693916088538413341/100000000000000000000)
  directionLo := (63132939860667176791/20000000000000000000)
  directionHi := (78916174825833970989/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree041.table
  base := (-11525580828528105420354609741582226921049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-23579095718029529275476198400277760000000000000000)
      constant := (276592074930470315595189577753209840895638316065256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree041.table
  base := (-720404457586809987933637873271022708839/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-47169336165239929901499579641528820000000000000000)
      constant := (553451188205130767638288734702906727096521510048512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63132939860667176791/20000000000000000000)
  centralHi := (78916174825833970989/25000000000000000000)
  directionLo := (159793075136191445233/50000000000000000000)
  directionHi := (319586150272382890467/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree042.table
  base := (-2241331092294100980024995124739964702283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-8033074315709141562110142739487628000000000000000)
      constant := (96442576078210938935376421671500660750465521366920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree042.table
  base := (-11207467227868295163612049051513394860299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-16069954148699556268309567424673456000000000000000)
      constant := (192978374731039681136971695156239592468230956311504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159793075136191445233/50000000000000000000)
  centralHi := (319586150272382890467/100000000000000000000)
  directionLo := (10108126975977262307/3125000000000000000)
  directionHi := (12938402529250895753/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree043.table
  base := (-10847985543197269197062674967988911826277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-24619350176225320097184658036648008000000000000000)
      constant := (302352392588053539566632538366875727791931656940488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree043.table
  base := (-5424362656687275616014502219393113681553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-49250388726957407708357824906511916000000000000000)
      constant := (604997365704086489095154820172812209676967744404128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10108126975977262307/3125000000000000000)
  centralHi := (12938402529250895753/4000000000000000000)
  directionLo := (327288126220972721311/100000000000000000000)
  directionHi := (10227753944405397541/3125000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree044.table
  base := (-2090095768506989455697244617093531621403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-25139477405323215508038887854833132000000000000000)
      constant := (315665759490892559115163262123136562412090740347160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree044.table
  base := (-10451152801323936472116880583896114975223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-50290915007816146611786947539003464000000000000000)
      constant := (631637296109062179772681179033684744008355752351024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327288126220972721311/100000000000000000000)
  centralHi := (10227753944405397541/3125000000000000000)
  directionLo := (13242877187372357917/4000000000000000000)
  directionHi := (165535964842154473963/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree045.table
  base := (-10014939609371862297149692048989187992307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-8553201544807036972964372557672752000000000000000)
      constant := (109755851874535263388150261619843250800849297440936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree045.table
  base := (-10015553436056145804564311498926404094357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-17110480429558295171738690057165004000000000000000)
      constant := (219618123037524445838731771553268155166385806938672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13242877187372357917/4000000000000000000)
  centralHi := (165535964842154473963/50000000000000000000)
  directionLo := (83703243546975467873/25000000000000000000)
  directionHi := (334812974187901871493/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree046.table
  base := (-9542080709566119530578280620261700963497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-26179731863519006329747347491203380000000000000000)
      constant := (343157538722968630296505937386670205763106071576168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree046.table
  base := (-4771319807772557753784536972819222491907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-52371967569533624418645192803986560000000000000000)
      constant := (686648100506186064951560673401372328194335591780832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83703243546975467873/25000000000000000000)
  centralHi := (334812974187901871493/100000000000000000000)
  directionLo := (67702535475181513003/20000000000000000000)
  directionHi := (42314084671988445627/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree047.table
  base := (-9032534288625448184493517763458220605067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-26699859092616901740601577309388504000000000000000)
      constant := (357335493958087750638706656894851883473031256568248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree047.table
  base := (-9033043052863530952600514157760670237451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-53412493850392363322074315436478108000000000000000)
      constant := (715018060922034662839873236650911143023452338117488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67702535475181513003/20000000000000000000)
  centralHi := (42314084671988445627/12500000000000000000)
  directionLo := (42771547530868490523/12500000000000000000)
  directionHi := (68434476049389584837/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree048.table
  base := (-4243430574767435979482569839670785410639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-9073328773904932383818602375857876000000000000000)
      constant := (123933743581134034609855038916919172387561877792144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree048.table
  base := (-424366207590692285671803720019755575661/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-18151006710417034075167812689656552000000000000000)
      constant := (247987956486772227963534853989021568867183345053120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42771547530868490523/12500000000000000000)
  centralHi := (68434476049389584837/20000000000000000000)
  directionLo := (69158670566608943317/20000000000000000000)
  directionHi := (172896676416522358293/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree049.table
  base := (-7905559005774381122689381399161841465503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-27740113550812692562310036945758752000000000000000)
      constant := (386554579933943924101327058609437789545934476399832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree049.table
  base := (-7905980257795464079334331328116875245939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-55493546412109841128932560701461204000000000000000)
      constant := (773485188081276595116463785503677588673748185422832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69158670566608943317/20000000000000000000)
  centralHi := (172896676416522358293/50000000000000000000)
  directionLo := (349376799348747814179/100000000000000000000)
  directionHi := (17468839967437390709/5000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree050.table
  base := (-7289069749561245180705216687297742995181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-28260240779910587973164266763943876000000000000000)
      constant := (401595391355269779752154925188728651340872100505864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree050.table
  base := (-3644726461981399650707876714389143454897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-56534072692968580032361683333952752000000000000000)
      constant := (803581716666484525730329054149685947203687801831072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349376799348747814179/100000000000000000000)
  centralHi := (17468839967437390709/5000000000000000000)
  directionLo := (35292386286964477181/10000000000000000000)
  directionHi := (352923862869644771811/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree051.table
  base := (-6637785857198018157508995022431930812253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-9593456003002827794672832194043000000000000000000)
      constant := (138974510542213708979734917908200367799617521993944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree051.table
  base := (-6638134314569454354266408986716967668169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-19191532991275772978596935322148100000000000000000)
      constant := (278084396222186450145735459723801755097419056631024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35292386286964477181/10000000000000000000)
  centralHi := (352923862869644771811/100000000000000000000)
  directionLo := (89108907397944954329/25000000000000000000)
  directionHi := (356435629591779817317/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree052.table
  base := (-5952056037704878624402872918888102090171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-29300495238106378794872726400314124000000000000000)
      constant := (432538882241370184390960934145680558375534209626424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree052.table
  base := (-186011651615210070771669317924706668513/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-58615125254686057839219928598935848000000000000000)
      constant := (865499367263161252950306463671204407722386853841408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89108907397944954329/25000000000000000000)
  centralHi := (356435629591779817317/100000000000000000000)
  directionLo := (17995656635848627789/5000000000000000000)
  directionHi := (359913132716972555781/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree053.table
  base := (-5232190217319828026767688020460348642419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64121520000000000000000000000000000000000000000
      center := (397381959)
      previous := (0)
      next := (352839825)
      square := (9263716353270625040194907813904000000000000000)
      linear := (-562653254098193852938244456952816000000000000000)
      constant := (8461157318355984318394176983441934884531815724312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree053.table
  base := (-1308119549471461585529118816463519434631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 128243040000000000000000000000000000000000000000
      center := (794971593)
      previous := (0)
      next := (705471975)
      square := (18527432706541250080389815627808000000000000000)
      linear := (-1125578330859335787597151910026932000000000000000)
      constant := (16930566829855128827153909506239671112441535712704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17995656635848627789/5000000000000000000)
  centralHi := (359913132716972555781/100000000000000000000)
  directionLo := (22709834750214234799/6250000000000000000)
  directionHi := (72671471200685551357/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree054.table
  base := (-895692788133701986472705328067606978569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-10113583232100723205527062012228124000000000000000)
      constant := (154876934959642964226439397695747571670315343273560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree054.table
  base := (-2239362827844444769009397453130215101769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-20232059272134511882026057954639648000000000000000)
      constant := (309905008568063208432639941963225386904883160353248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22709834750214234799/6250000000000000000)
  centralHi := (72671471200685551357/20000000000000000000)
  directionLo := (22923077313513597553/6250000000000000000)
  directionHi := (366769237016217560849/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree055.table
  base := (-230695141199095247993233667812858183/625000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-30860876925400065027435415854869496000000000000000)
      constant := (481107199980281892848367100387246119768183836032000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree055.table
  base := (-3691360054370993123802471924234305024353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-61736704097262274549507296496410492000000000000000)
      constant := (962684152021216862227301760420668591297365395408464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22923077313513597553/6250000000000000000)
  centralHi := (366769237016217560849/100000000000000000000)
  directionLo := (23134354381754540533/6250000000000000000)
  directionHi := (370149670108072648529/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree056.table
  base := (-358797896061965674675274036987278004033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-31381004154497960438289645673054620000000000000000)
      constant := (497870449092408828314690443846982383381678727377216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree056.table
  base := (-717649796455440822071320589459745466551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-62777230378121013452936419128902040000000000000000)
      constant := (996227272902845283284401937716329790015357566633152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23134354381754540533/6250000000000000000)
  centralHi := (370149670108072648529/100000000000000000000)
  directionLo := (37349950915733697513/10000000000000000000)
  directionHi := (373499509157336975131/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree057.table
  base := (-2016440648752526661250910035688704386377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-10633710461198618616381291830413248000000000000000)
      constant := (171640162097435859964105591558241711565982883058296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree057.table
  base := (-20166368434608077930177309832522758079/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-21272585552993250785455180587131196000000000000000)
      constant := (343448085543330465748663849664230825053808391438400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37349950915733697513/10000000000000000000)
  centralHi := (373499509157336975131/100000000000000000000)
  directionLo := (376819570086836497753/100000000000000000000)
  directionHi := (188409785043418248877/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree058.table
  base := (-564733677611143761821272135956538015859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-32421258612693751259998105309424868000000000000000)
      constant := (532257252904112138118623580195820969361944570231792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree058.table
  base := (-282411377873401384044744085999351863287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-64858282939838491259794664393885136000000000000000)
      constant := (1065034985967191232339711361741560679095275107423424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376819570086836497753/100000000000000000000)
  centralHi := (188409785043418248877/50000000000000000000)
  directionLo := (95027658296178736801/25000000000000000000)
  directionHi := (76022126636942989441/20000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree059.table
  base := (-104808500281760532741930682965948207289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-32941385841791646670852335127609992000000000000000)
      constant := (549880696689489175365266448772180753852697954951632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree059.table
  base := (-104889372976443217218689683004541729871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-65898809220697230163223787026376684000000000000000)
      constant := (1100299356544234816158295140395051269213397532012896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95027658296178736801/25000000000000000000)
  centralHi := (76022126636942989441/20000000000000000000)
  directionLo := (383373445245939741/100000000000000000)
  directionHi := (383373445245939741001/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree060.table
  base := (74297353483999919069786890333627784931/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-11153837690296514027235521648598372000000000000000)
      constant := (189263590376817961067254768557176860865417489067120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree060.table
  base := (742826716119380850121585256243259842863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-22313111833851989688884303219622744000000000000000)
      constant := (378712425140860084185682280891818845831773656381552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383373445245939741/100000000000000000)
  centralHi := (383373445245939741001/100000000000000000000)
  directionLo := (386608721551128736499/100000000000000000000)
  directionHi := (773217443102257473/200000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree061.table
  base := (1728182332572578083488442145118147807651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-33981640299987437492560794763980240000000000000000)
      constant := (585987434793757370690402572977697048700159623672456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree061.table
  base := (432012271858500695863314763627498541863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-67979861782414707970082032291359780000000000000000)
      constant := (1172548659824854883984809046944807082145806461730624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386608721551128736499/100000000000000000000)
  centralHi := (773217443102257473/200000000000000000)
  directionLo := (194908573848775845549/50000000000000000000)
  directionHi := (389817147697551691099/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree062.table
  base := (686475194465619727881771535590538353707/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-34501767529085332903415024582165364000000000000000)
      constant := (604470650767315069316426745141145237637389398062368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree062.table
  base := (1372889936560540798463365958475022720619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-69020388063273446873511154923851328000000000000000)
      constant := (1209533436008385427941587997084343934684269263162656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194908573848775845549/50000000000000000000)
  centralHi := (389817147697551691099/100000000000000000000)
  directionLo := (392999381295583551021/100000000000000000000)
  directionHi := (196499690647791775511/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree063.table
  base := (759206417716611879602167142438322083607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-11673964919394409438089751466783496000000000000000)
      constant := (207746795386765504220942342587099851761212289983320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree063.table
  base := (1897961200324108131407471393399879962089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-23353638114710728592313425852114292000000000000000)
      constant := (415697179422000284838007009104362227489972602657312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392999381295583551021/100000000000000000000)
  centralHi := (196499690647791775511/50000000000000000000)
  directionLo := (198078026771249984861/50000000000000000000)
  directionHi := (396156053542499969723/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree064.table
  base := (2439245004941833256009917582899240084377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-35542021987281123725123484218535612000000000000000)
      constant := (642296611659503405129326923669940803979184923826224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree064.table
  base := (4878390515299320090574999810938489039403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-71101440624990924680369400188834424000000000000000)
      constant := (1285222908039364846843384711212367570563324518677136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198078026771249984861/50000000000000000000)
  centralHi := (396156053542499969723/100000000000000000000)
  directionLo := (79857554136856643241/20000000000000000000)
  directionHi := (199643885342141608103/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree065.table
  base := (1498299413836813496529073773377243785687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-36062149216379019135977714036720736000000000000000)
      constant := (661639301135543926404860713786411598134914659305888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree065.table
  base := (5993107422115370057527231662130678948061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-72141966905849663583798522821325972000000000000000)
      constant := (1323927493131856695454029369796997331196485727150832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79857554136856643241/20000000000000000000)
  centralHi := (199643885342141608103/50000000000000000000)
  directionLo := (402395115375027105851/100000000000000000000)
  directionHi := (100598778843756776463/25000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree066.table
  base := (7140086477842774732943087783135209638701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-12194092148492304848943981284968620000000000000000)
      constant := (227089477097694344761244655169497335346675480803752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree066.table
  base := (7140004657469367876372255560800946027051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-24394164395569467495742548484605840000000000000000)
      constant := (454401749003187675069277750668920353237646731705904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402395115375027105851/100000000000000000000)
  centralHi := (100598778843756776463/25000000000000000000)
  directionLo := (405478647942574175279/100000000000000000000)
  directionHi := (5068483099282177191/1250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree067.table
  base := (1039886919403948497664623935717561124251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-37102403674574809957686173673090984000000000000000)
      constant := (701183981360125221691940804837875967693147038416448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree067.table
  base := (4159510587719413640719837276983102826809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-74223019467567141390656768086309068000000000000000)
      constant := (1403056128180296036116536915322395130557511344389216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405478647942574175279/100000000000000000000)
  centralHi := (5068483099282177191/1250000000000000000)
  directionLo := (408538907568171099181/100000000000000000000)
  directionHi := (204269453784085549591/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree068.table
  base := (9530169777834306030807653049133982768961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-37622530903672705368540403491276108000000000000000)
      constant := (721385932811879954253770467613810565991637817145816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree068.table
  base := (9530102535886113617164588342526728221579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-75263545748425880294085890718800616000000000000000)
      constant := (1443480099641741362260953682366136213214462148168848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408538907568171099181/100000000000000000000)
  centralHi := (204269453784085549591/50000000000000000000)
  directionLo := (51447051673396954119/12500000000000000000)
  directionHi := (411576413387175632953/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree069.table
  base := (10773261126098790723776362327408162640683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-12714219377590200259798211103153744000000000000000)
      constant := (247291423041760477478086215732567411569772460443416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree069.table
  base := (5386600091345530264971908397171931479921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-25434690676428206399171671117097388000000000000000)
      constant := (494825709463627120575692361078925025872987246932768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51447051673396954119/12500000000000000000)
  centralHi := (411576413387175632953/100000000000000000000)
  directionLo := (414591665517178386663/100000000000000000000)
  directionHi := (51823958189647298333/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree070.table
  base := (3012081507064591983198586735654235291147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-38662785361868496190248863127646356000000000000000)
      constant := (762648975560692553812309688733529010539686949488928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree070.table
  base := (12048270801928453003331154119038933916823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-77344598310143358100944135983783712000000000000000)
      constant := (1526047184987755981811184747371085773748418189908176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414591665517178386663/100000000000000000000)
  centralHi := (51823958189647298333/12500000000000000000)
  directionLo := (6524767906551645867/1562500000000000000)
  directionHi := (417585146019305335489/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree071.table
  base := (2671065157791034563660808021899918330203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47865360000000000000000000000000000000000000000
      center := (296637237)
      previous := (0)
      next := (263387475)
      square := (6915168545399198973666621325872000000000000000)
      linear := (-551872008323470304240888633039880000000000000000)
      constant := (11038169562925717651117585344781647987422882734040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree071.table
  base := (13355275750968613831535248294697524387631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 95730720000000000000000000000000000000000000000
      center := (593429499)
      previous := (0)
      next := (526619925)
      square := (13830337090798397947333242651744000000000000000)
      linear := (-1104015839309888690202440262201060000000000000000)
      constant := (22087186523484918514057787538695294494184547472432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6524767906551645867/1562500000000000000)
  centralHi := (417585146019305335489/100000000000000000000)
  directionLo := (42055731979793336517/10000000000000000000)
  directionHi := (420557319797933365171/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree072.table
  base := (7347112940423605823365393672791120680807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-13234346606688095670652440921338868000000000000000)
      constant := (268352482537489894878610221825827907528633954822128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree072.table
  base := (918386284407675476054433143809442125551/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-26475216957286945302600793749588936000000000000000)
      constant := (536968759831579465374170461721253429099141472798464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42055731979793336517/10000000000000000000)
  centralHi := (420557319797933365171/100000000000000000000)
  directionLo := (105877158860893431543/25000000000000000000)
  directionHi := (423508635443573726173/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree073.table
  base := (4016248873034229533227915846814494164769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-40223167049162182422811552582201728000000000000000)
      constant := (826691191023717490454477385585080114256173717052256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree073.table
  base := (4016238608143543907935279459913272792857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-80466177152719574811231503881258356000000000000000)
      constant := (1654195273057028237991678973956333098398271765663936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105877158860893431543/25000000000000000000)
  centralHi := (423508635443573726173/100000000000000000000)
  directionLo := (85287905204650083101/20000000000000000000)
  directionHi := (213219763011625207753/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree074.table
  base := (17467607123769092239613920941865054676071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-40743294278260077833665782400386852000000000000000)
      constant := (848611259856078915336744191946324996385777734783976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree074.table
  base := (17467569937944836967286116407157214787681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-81506703433578313714660626513749904000000000000000)
      constant := (1698057205190621969158501991795004170106217379748272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85287905204650083101/20000000000000000000)
  centralHi := (213219763011625207753/50000000000000000000)
  directionLo := (2146752049111582337/500000000000000000)
  directionHi := (429350409822316467401/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree075.table
  base := (18902036230760553076316941600487545807217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-13754473835785991081506670739523992000000000000000)
      constant := (290272548589362440212338288549834704298203473117384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree075.table
  base := (3780400511592810724387207454527972888943/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-27515743238145684206029916382080484000000000000000)
      constant := (580830686412422482693682249324089982281788088909360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2146752049111582337/500000000000000000)
  centralHi := (429350409822316467401/100000000000000000000)
  directionLo := (432241691041305895731/100000000000000000000)
  directionHi := (108060422760326473933/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree076.table
  base := (1018413045137715705443004816231698721281/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-41783548736455868655374242036757100000000000000000)
      constant := (893310341313638119643582875966665140584202971114720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree076.table
  base := (10184115207666329821286661749470616179141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-83587755995295791521518871778733000000000000000000)
      constant := (1787499820327224508993464089699459776220554000143584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432241691041305895731/100000000000000000000)
  centralHi := (108060422760326473933/25000000000000000000)
  directionLo := (435113760451108208793/100000000000000000000)
  directionHi := (217556880225554104397/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree077.table
  base := (21866261579447809459709453594690007926989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-42303675965553764066228471854942224000000000000000)
      constant := (916089339845278751781419892332556101106580093627384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree077.table
  base := (54665584949588772217220216285009548093/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-84628282276154530424947994411224548000000000000000)
      constant := (1833080475186038092260483325494101520583121748166400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435113760451108208793/100000000000000000000)
  centralHi := (217556880225554104397/50000000000000000000)
  directionLo := (43796699600947217327/10000000000000000000)
  directionHi := (437966996009472173271/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree078.table
  base := (5849005199259146235324907900834753799369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-14274601064883886492360900557709116000000000000000)
      constant := (313051545142679692716185836876196633355918628267552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree078.table
  base := (23395995815045423094283910027114614585379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-28556269519004423109459039014572032000000000000000)
      constant := (626411337320791976354890744391198136898381305104816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43796699600947217327/10000000000000000000)
  centralHi := (437966996009472173271/100000000000000000000)
  directionLo := (220400881720796236869/50000000000000000000)
  directionHi := (440801763441592473739/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree079.table
  base := (2495752296224971605118712643836228010593/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-43343930423749554887936931491312472000000000000000)
      constant := (962506222762638661455215548574386261018607360852080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree079.table
  base := (12478750176298410666396474147391252826831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-86709334837872008231806239676207644000000000000000)
      constant := (1925960420074605010776598387219837735843366850666144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220400881720796236869/50000000000000000000)
  centralHi := (440801763441592473739/100000000000000000000)
  directionLo := (443618416787304140041/100000000000000000000)
  directionHi := (221809208393652070021/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree080.table
  base := (26550754150937852718993412054333952534207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-43864057652847450298791161309497596000000000000000)
      constant := (986144097117038110223712682423366022807736385623592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree080.table
  base := (26550733690991708796568888854816185054683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-87749861118730747135235362308699192000000000000000)
      constant := (1973259690074042411334890300953242614926860105028496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443618416787304140041/100000000000000000000)
  centralHi := (221809208393652070021/50000000000000000000)
  directionLo := (446417298917202495323/100000000000000000000)
  directionHi := (111604324729300623831/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree081.table
  base := (14087850964257597456669802193543577663889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-14794728293981781903215130375894240000000000000000)
      constant := (336689418088472450497126728314136316547364694995856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree081.table
  base := (5635136683248195008176754696197685101867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-29596795799863162012888161647063580000000000000000)
      constant := (673710604507682436624270449364469931651097514841840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446417298917202495323/100000000000000000000)
  centralHi := (111604324729300623831/25000000000000000000)
  directionLo := (449198742019818618231/100000000000000000000)
  directionHi := (56149842752477327279/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree082.table
  base := (745808879746452853866096074469869897241/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-44904312111043241120499620945867844000000000000000)
      constant := (1034278690433766128974279843489501065426827385979840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree082.table
  base := (29832338441945238729400376768880754029389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-89830913680448224942093607573682288000000000000000)
      constant := (2069576782886325842011898442909891647559371801923568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449198742019818618231/100000000000000000000)
  centralHi := (56149842752477327279/12500000000000000000)
  directionLo := (225981534030904944043/50000000000000000000)
  directionHi := (451963068061809888087/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree083.table
  base := (7880176004132537570578497960014391312811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-45424439340141136531353850764052968000000000000000)
      constant := (1058775402251362766873153615208301335998467420005664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree083.table
  base := (31520688866686374320353068931282708759023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-90871439961306963845522730206173836000000000000000)
      constant := (2118594591434001815880089927346128132179666205834576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225981534030904944043/50000000000000000000)
  centralHi := (451963068061809888087/100000000000000000000)
  directionLo := (227355294611485149959/50000000000000000000)
  directionHi := (454710589222970299919/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree084.table
  base := (2077546221839985389883430080859298620939/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-15314855523079677314069360194079364000000000000000)
      constant := (361186128902499221586287782905002272712827286872448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree084.table
  base := (3324072584683740127675067552500428829201/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-30637322080721900916317284279555128000000000000000)
      constant := (722728411051722368614645841294721595167033327195040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227355294611485149959/50000000000000000000)
  centralHi := (454710589222970299919/100000000000000000000)
  directionLo := (457441608307724309939/100000000000000000000)
  directionHi := (22872080415386215497/5000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree085.table
  base := (6998490775049416418465946677153078429717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-46464693798336927353062310400423216000000000000000)
      constant := (1108627641112869301329520708615083752282205681060760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree085.table
  base := (8748110370777038489378582814236616658389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-92952492523024441652380975471156932000000000000000)
      constant := (2218348702680768093078689068929832803916232673486272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457441608307724309939/100000000000000000000)
  centralHi := (22872080415386215497/5000000000000000000)
  directionLo := (460156419134639593007/100000000000000000000)
  directionHi := (28759776195914974563/6250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree086.table
  base := (9193959981255487743590855746981689335873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-46984821027434822763916540218608340000000000000000)
      constant := (1133983163065143783891967331094503706246540106483552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree086.table
  base := (9193957179832549474399003270061623058741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-93993018803883180555810098103648480000000000000000)
      constant := (2269084995214810976408800341709077556301805341547968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460156419134639593007/100000000000000000000)
  centralHi := (28759776195914974563/6250000000000000000)
  directionLo := (92571061381075402147/20000000000000000000)
  directionHi := (28928456681586063171/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree087.table
  base := (4823861422977615942648242174065434729833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-15834982752177572724923590012264488000000000000000)
      constant := (386541650139408372856735596141275725511305895793728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree087.table
  base := (7718176250429911783210905486812165246249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-31677848361580639819746406912046676000000000000000)
      constant := (773464702157660331285176891995834246866424996486480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92571061381075402147/20000000000000000000)
  centralHi := (28928456681586063171/6250000000000000000)
  directionLo := (465538548554389188587/100000000000000000000)
  directionHi := (116384637138597297147/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree088.table
  base := (40437602609997329988293375235976733701727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-48025075485630613585624999854978588000000000000000)
      constant := (1185553001254833214500855075695831606302826797884712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree088.table
  base := (40437593450442400902066893684625893494627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-96074071365600658362668343368631576000000000000000)
      constant := (2372276032627870216814517377291933028975676107774224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465538548554389188587/100000000000000000000)
  centralHi := (116384637138597297147/25000000000000000000)
  directionLo := (468206413080581390517/100000000000000000000)
  directionHi := (234103206540290695259/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree089.table
  base := (42315968563188838156622290425280581878521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-48545202714728508996479229673163712000000000000000)
      constant := (1211767313862030897091485506228932502633636675921176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree089.table
  base := (42315960283398954628512770040626801392521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-97114597646459397266097466001123124000000000000000)
      constant := (2424730770260097051408623321313434904060081569410352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468206413080581390517/100000000000000000000)
  centralHi := (234103206540290695259/50000000000000000000)
  directionLo := (58857395232757371879/12500000000000000000)
  directionHi := (470859161862058975033/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree090.table
  base := (22112992370021390027889243741084059235881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-16355109981275468135777819830449612000000000000000)
      constant := (412755962236460176231481641197646260351777373182224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree090.table
  base := (5528247157042080027276653768216572755509/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-32718374642439378723175529544538224000000000000000)
      constant := (825919438771559726960613190570228910348806799490688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58857395232757371879/12500000000000000000)
  centralHi := (470859161862058975033/100000000000000000000)
  directionLo := (473497048955003825933/100000000000000000000)
  directionHi := (236748524477501912967/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree091.table
  base := (46167647116842093260863510970705010977539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-49585457172924299818187689309533960000000000000000)
      constant := (1265054718429445782618850641304367269860131378658184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree091.table
  base := (5770955044175761967556260334520941832457/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-99195650208176875072955711266106220000000000000000)
      constant := (2531358668062091534347071606218776623153516149209472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473497048955003825933/100000000000000000000)
  centralHi := (236748524477501912967/50000000000000000000)
  directionLo := (476120321377647066589/100000000000000000000)
  directionHi := (47612032137764706659/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree092.table
  base := (24070476049143184152274598532799860440181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-50105584402022195229041919127719084000000000000000)
      constant := (1292127807800385185172865056685798417216450112828272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree092.table
  base := (48140945986445185667163497232797442166829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-100236176489035613976384833898597768000000000000000)
      constant := (2585531823063502964357364315690676837944801192036848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476120321377647066589/100000000000000000000)
  centralHi := (47612032137764706659/10000000000000000000)
  directionLo := (119682304845059113597/25000000000000000000)
  directionHi := (478729219380236454389/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree093.table
  base := (12536474117940920010707762613890312346287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-16875237210373363546632049648634736000000000000000)
      constant := (439829051243470556453860432656136702499158734160096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree093.table
  base := (5014589094931730691122599854014246993767/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-33758900923298117626604652177029772000000000000000)
      constant := (880092593046580178782111551651023268909317226659680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119682304845059113597/25000000000000000000)
  centralHi := (478729219380236454389/100000000000000000000)
  directionLo := (240661988350916771541/50000000000000000000)
  directionHi := (481323976701833543083/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree094.table
  base := (3261404835407576983328688438708139550469/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-51145838860217986050750378764089332000000000000000)
      constant := (1347132755243916960966701550702525930720726426596224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree094.table
  base := (52182472377142578306336194747645195047567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-102317229050753091783243079163580864000000000000000)
      constant := (2695596534343579452777274872956077968567752564423504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240661988350916771541/50000000000000000000)
  centralHi := (481323976701833543083/100000000000000000000)
  directionLo := (120976205203679371099/25000000000000000000)
  directionHi := (483904820814717484397/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree095.table
  base := (27125346108603592478121744583288134431177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-51665966089315881461604608582274456000000000000000)
      constant := (1375064611469081486152655854828263952593528889067824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree095.table
  base := (1356267192747370027600776913674681112511/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-103357755331611830686672201796072412000000000000000)
      constant := (2751488086935000339952305384001091982627586446769280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120976205203679371099/25000000000000000000)
  centralHi := (483904820814717484397/100000000000000000000)
  directionLo := (486471973157118757041/100000000000000000000)
  directionHi := (243235986578559378521/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree096.table
  base := (56350538731313320013018828221241417342761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-17395364439471258957486279466819860000000000000000)
      constant := (467760907208936651041225531821819278874984213492872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree096.table
  base := (56350534659894306560035635458264936329657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-34799427204156856530033774809521320000000000000000)
      constant := (935984145119698174320614832255207375123234925312528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486471973157118757041/100000000000000000000)
  centralHi := (243235986578559378521/50000000000000000000)
  directionLo := (244512824677478373899/50000000000000000000)
  directionHi := (489025649354956747799/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree097.table
  base := (58482014860099157069378100242608595204359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-52706220547511672283313068218644704000000000000000)
      constant := (1431787085020850087521520681320058337764711511440104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree097.table
  base := (29241005591388876359309699731229611885321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-105438807893329308493530447061055508000000000000000)
      constant := (2864989578226332541669991379142192512806653182007904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244512824677478373899/50000000000000000000)
  centralHi := (489025649354956747799/100000000000000000000)
  directionLo := (491566059433209592699/100000000000000000000)
  directionHi := (4915660594332095927/1000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree098.table
  base := (947579980822243261560309739884850893509/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-53226347776609567694167298036829828000000000000000)
      constant := (1460577701028967430318300206958859348838740648480256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree098.table
  base := (60645115451571296490135228487737759175543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-106479334174188047396959569693547056000000000000000)
      constant := (2922599514294941993993759519749179872185135498244816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491566059433209592699/100000000000000000000)
  centralHi := (4915660594332095927/1000000000000000000)
  directionLo := (247046704008751340267/50000000000000000000)
  directionHi := (98818681603500536107/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree099.table
  base := (62839848832550350932442340119512581150979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-17915491668569154368340509285004984000000000000000)
      constant := (496551523031687616311912911693465770023792617243608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree099.table
  base := (62839845833533969730993857282885477483257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-35839953485015595433462897442012868000000000000000)
      constant := (993594080818389417970193528661506210075937820646928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247046704008751340267/50000000000000000000)
  centralHi := (98818681603500536107/20000000000000000000)
  directionLo := (7759498351975990967/1562500000000000000)
  directionHi := (496607894526463421889/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree100.table
  base := (16266550894357560271693066175034817214473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-54266602234805358515875757673200076000000000000000)
      constant := (1519017688722131654291116826246414802893540504889952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree100.table
  base := (8133275108684259943373461140746536960881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-108560386735905525203817814958530152000000000000000)
      constant := (3039537761715216074631106800696222739819835397973376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7759498351975990967/1562500000000000000)
  centralHi := (496607894526463421889/100000000000000000000)
  directionLo := (499109713355354020257/100000000000000000000)
  directionHi := (249554856677677010129/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree101.table
  base := (8415522712524246212959511290642490904697/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-54786729463903253926729987491385200000000000000000)
      constant := (1548667059465974124364878267268665468389962703448256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree101.table
  base := (67324179255273521510460532026552858546787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-109600913016764264107246937591021700000000000000000)
      constant := (3098866071188691883931885686165196875418868719696144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499109713355354020257/100000000000000000000)
  centralHi := (249554856677677010129/50000000000000000000)
  directionLo := (125399763512865199653/25000000000000000000)
  directionHi := (501599054051460798613/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree102.table
  base := (17403445508154883883316239386208843998829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-18435618897667049779194739103190108000000000000000)
      constant := (526200893643192318647941252867518802010177742147232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree102.table
  base := (2175430619543233530374784508920448094127/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-36880479765874334336892020074504416000000000000000)
      constant := (1052922390027795334367503537638978035415105908461056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125399763512865199653/25000000000000000000)
  centralHi := (501599054051460798613/100000000000000000000)
  directionLo := (504076101481687909983/100000000000000000000)
  directionHi := (15752378171302747187/3125000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree103.table
  base := (17983750882640597888799823902315811928393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-55826983922099044748438447127755448000000000000000)
      constant := (1608824552758093831118278386027121443024713034728032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree103.table
  base := (17983750384520101643066359319544475611751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-111681965578481741914105182856004796000000000000000)
      constant := (3219241057691251334606145045873149582439324328816448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504076101481687909983/100000000000000000000)
  centralHi := (15752378171302747187/3125000000000000000)
  directionLo := (506541035992774789633/100000000000000000000)
  directionHi := (253270517996387394817/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree104.table
  base := (74287845260759959472449132010032287961803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-56347111151196940159292676945940572000000000000000)
      constant := (1639332674634361009966761910931540401431899104592968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree104.table
  base := (74287843462294072778918709963082717516209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-112722491859340480817534305488496344000000000000000)
      constant := (3280287733379450498398771135053504573968421424607408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506541035992774789633/100000000000000000000)
  centralHi := (253270517996387394817/50000000000000000000)
  directionLo := (254497016782265151891/50000000000000000000)
  directionHi := (508994033564530303783/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree105.table
  base := (76672306389042158238714430992769670170961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-18955746126764945190048968921375232000000000000000)
      constant := (556709015424963582917550335124034066711560533219272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree105.table
  base := (38336152382919674011091721876302895709911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-37921006046733073240321142706995964000000000000000)
      constant := (1113969065527452386335588521093864654525134871518688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254497016782265151891/50000000000000000000)
  centralHi := (508994033564530303783/100000000000000000000)
  directionLo := (51143526595645204687/10000000000000000000)
  directionHi := (511435265956452046871/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree106.table
  base := (79088386169797706754453730756371512594227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 64121520000000000000000000000000000000000000000
      center := (397381959)
      previous := (0)
      next := (352839825)
      square := (9263716353270625040194907813904000000000000000)
      linear := (-1082780483196089263792474275137940000000000000000)
      constant := (32098257875967763877504176589248125107224097846504) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree106.table
  base := (39544192352450950621813444914233277673041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 128243040000000000000000000000000000000000000000
      center := (794971593)
      previous := (0)
      next := (705471975)
      square := (18527432706541250080389815627808000000000000000)
      linear := (-2166104611718074691026274542518480000000000000000)
      constant := (64228291448951123737254324789323592459590980776928) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51143526595645204687/10000000000000000000)
  centralHi := (511435265956452046871/100000000000000000000)
  directionLo := (256932450424038241301/50000000000000000000)
  directionHi := (513864900848076482603/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree107.table
  base := (81536083936562081957811272725961404563337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-57907492838490626391855366400495944000000000000000)
      constant := (1732574537862069213534526372624642913976261354974872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree107.table
  base := (81536082614643735932436650507819052498473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-115844070701916697527821673385970988000000000000000)
      constant := (3466864483563725212967615420543927141155315996252976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256932450424038241301/50000000000000000000)
  centralHi := (513864900848076482603/100000000000000000000)
  directionLo := (516283101973384473777/100000000000000000000)
  directionHi := (258141550986692236889/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree108.table
  base := (42007699546803697106470144084597742284461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-19475873355862840600903198739560356000000000000000)
      constant := (588075885793256450182299838891695111244262621342544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree108.table
  base := (84015397900809029988401426546413314475911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-38961532327591812143750265339487512000000000000000)
      constant := (1176734102162131835305957896875510966029264739023344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516283101973384473777/100000000000000000000)
  centralHi := (258141550986692236889/50000000000000000000)
  directionLo := (259345014624783537439/50000000000000000000)
  directionHi := (518690029249567074879/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree109.table
  base := (86526331108427271713039959668565078146147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-58947747296686417213563826036866192000000000000000)
      constant := (1796167025798422771304173553206196296607143557252232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree109.table
  base := (5407895627013969466242474723145749919737/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-117925123263634175334679918650954084000000000000000)
      constant := (3594112915201387598879468174470022834545323089064704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259345014624783537439/50000000000000000000)
  centralHi := (518690029249567074879/100000000000000000000)
  directionLo := (260542919450219076677/50000000000000000000)
  directionHi := (104217167780087630671/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree110.table
  base := (89068879505021293218829626280205169381273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-59467874525784312624418055855051316000000000000000)
      constant := (1828392642956263561994682795880451927274698826763288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree110.table
  base := (89068878534092042902987942068618065716573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-118965649544492914238109041283445632000000000000000)
      constant := (3658596309385988881296385383375265445035989429480176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260542919450219076677/50000000000000000000)
  centralHi := (104217167780087630671/20000000000000000000)
  directionLo := (523470683574763354463/100000000000000000000)
  directionHi := (16358458861711354827/3125000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree111.table
  base := (91643043857893723936640363836474905895573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-19996000584960736011757428557745480000000000000000)
      constant := (620301502902896508765148824795854911503923280254696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree111.table
  base := (91643042982009290788854929271738990525727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-40002058608450551047179387971979060000000000000000)
      constant := (1241217496250578697766552108341612862850739090685808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523470683574763354463/100000000000000000000)
  centralHi := (16358458861711354827/3125000000000000000)
  directionLo := (1051689424919518067/200000000000000000)
  directionHi := (525844712459759033501/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree112.table
  base := (9424882378669042631279760759107476439007/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-60508128983980103446126515491421564000000000000000)
      constant := (1893702622926439571383841906940117677329565754923920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree112.table
  base := (47124411498303731283931341907052970407217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-121046702106210392044967286548428728000000000000000)
      constant := (3789281453040777456217623560749430105880146387808608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1051689424919518067/200000000000000000)
  centralHi := (525844712459759033501/100000000000000000000)
  directionLo := (528208071389999959629/100000000000000000000)
  directionHi := (52820807138999995963/10000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree113.table
  base := (24221554737851488736907872967881715065931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-61028256213077998856980745309606688000000000000000)
      constant := (1926786985493964867633158745327000703854969193824544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree113.table
  base := (48443109119386610782604196766645262809423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-122087228387069130948396409180920276000000000000000)
      constant := (3855483202022621666491770009178068406630361069358752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528208071389999959629/100000000000000000000)
  centralHi := (52820807138999995963/10000000000000000000)
  directionLo := (106112180590392153233/20000000000000000000)
  directionHi := (265280451475980383083/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree114.table
  base := (99555229048100108663706356365193626165459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-20516127814058631422611658375930604000000000000000)
      constant := (653385865435991048097933759689509611713805771220568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree114.table
  base := (19911045681074628940887696643277778473817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-41042584889309289950608510604470608000000000000000)
      constant := (1307419245163744180035721236039548291070704863605840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106112180590392153233/20000000000000000000)
  centralHi := (265280451475980383083/50000000000000000000)
  directionLo := (53290334658440320869/10000000000000000000)
  directionHi := (532903346584403208691/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree115.table
  base := (20451170761013939475722234745320206491327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-62068510671273789678689204945976936000000000000000)
      constant := (1993814455276127687220023970372489263713850482511560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree115.table
  base := (12781981653179195555488681157142849585121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-124168280948786608755254654445903372000000000000000)
      constant := (3989605053262432496570709303227956648115487006252416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53290334658440320869/10000000000000000000)
  centralHi := (532903346584403208691/100000000000000000000)
  directionLo := (26761776933740461339/5000000000000000000)
  directionHi := (535235538674809226781/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree116.table
  base := (26247023244856767730770349236678906145273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-62588637900371685089543434764162060000000000000000)
      constant := (2027757562315884572225994869046329391736211606189152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree116.table
  base := (3280877889272700571572339389348898701757/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-125208807229645347658683777078394920000000000000000)
      constant := (4057525155171582001412913333648673223772046925209088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26761776933740461339/5000000000000000000)
  centralHi := (535235538674809226781/100000000000000000000)
  directionLo := (537557612652048524679/100000000000000000000)
  directionHi := (13438940316301213117/2500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree117.table
  base := (53875973177021063123578899092750466926727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-21036255043156526833465888194115728000000000000000)
      constant := (687328972451151141470505953488754368834181838989808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree117.table
  base := (21550389176543578340041529948695241019401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-42083111170168028854037633236962156000000000000000)
      constant := (1375339347023835198347527373461982099761436035101520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537557612652048524679/100000000000000000000)
  centralHi := (13438940316301213117/2500000000000000000)
  directionLo := (53986969907545883367/10000000000000000000)
  directionHi := (539869699075458833671/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree118.table
  base := (110547413734809125362627113359783191886361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-63628892358567475911251894400532308000000000000000)
      constant := (2096502520322868562485805268773265513211287213320216) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree118.table
  base := (55273706654920624915810093418771809715651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-127289859791362825465542022343378016000000000000000)
      constant := (4195083710830638268908974066454723522908908170081824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53986969907545883367/10000000000000000000)
  centralHi := (539869699075458833671/100000000000000000000)
  directionLo := (27108596286025357071/5000000000000000000)
  directionHi := (542171925720507141421/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree119.table
  base := (5668724747410188921104298922694698807803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-64149019587665371322106124218717432000000000000000)
      constant := (2131304371165158787972595913672207407600842719379360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree119.table
  base := (113374494565059369955515370995809101197391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-128330386072221564368971144975869564000000000000000)
      constant := (4264722164331368747758477657271302853030271628115792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27108596286025357071/5000000000000000000)
  centralHi := (542171925720507141421/100000000000000000000)
  directionLo := (544464417661190922523/100000000000000000000)
  directionHi := (136116104415297730631/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree120.table
  base := (11623318983909972762293705554653740328309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-21556382272254422244320118012300852000000000000000)
      constant := (722130823275868443414582622836370995962477673937680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree120.table
  base := (58116594746843081211716080029929579102957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-43123637451026767757466755869453704000000000000000)
      constant := (1444977800489519578455089221128493272742295664631456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544464417661190922523/100000000000000000000)
  centralHi := (136116104415297730631/25000000000000000000)
  directionLo := (546747297349329735399/100000000000000000000)
  directionHi := (2733736486746648677/500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree121.table
  base := (119123498268816855490991039607215653841503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-65189274045861162143814583855087680000000000000000)
      constant := (2201766816263078575690276164550596671418188360656168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree121.table
  base := (59561748978719675606436804818191774670869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-130411438633939042175829390240852660000000000000000)
      constant := (4405717422148219412616550267136796395284944744018656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546747297349329735399/100000000000000000000)
  centralHi := (2733736486746648677/500000000000000000)
  directionLo := (274510342345444711141/50000000000000000000)
  directionHi := (549020684690889422283/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree122.table
  base := (6102271005668838888356954267085707428347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-65709401274959057554668813673272804000000000000000)
      constant := (2237427410429445207349238696866396062241575477108640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree122.table
  base := (122045419832700017420293160802457706036187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-131451964914797781079258512873344208000000000000000)
      constant := (4477074226286328469915292797786833230675586945708944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274510342345444711141/50000000000000000000)
  centralHi := (549020684690889422283/100000000000000000000)
  directionLo := (137821174279868380873/25000000000000000000)
  directionHi := (551284697119473523493/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree123.table
  base := (12499895526194350425594051905676682122589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-22076509501352317655174347830485976000000000000000)
      constant := (757791417429679424253946891400406373507211116603280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree123.table
  base := (62499477504478464135455755501744731908613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-44164163731885506660895878501945252000000000000000)
      constant := (1516334604602590912034004329988527599732940884339104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137821174279868380873/25000000000000000000)
  centralHi := (551284697119473523493/100000000000000000000)
  directionLo := (27676972483355467973/5000000000000000000)
  directionHi := (553539449667109359461/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree124.table
  base := (31996025903857398549521542867303086300853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-66749655733154848376377273309643052000000000000000)
      constant := (2309607341808183494161778748707885688519199679119072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree124.table
  base := (31996025846854003458240599492600659821839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-133533017476515258886116758138327304000000000000000)
      constant := (4621506184645403056307992664046079873777040025111872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27676972483355467973/5000000000000000000)
  centralHi := (553539449667109359461/100000000000000000000)
  directionLo := (555785055032449511901/100000000000000000000)
  directionHi := (277892527516224755951/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree125.table
  base := (131000865085250225979698223966096898031179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-67269782962252743787231503127828176000000000000000)
      constant := (2346126678956775846471756216620537245065934285822024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree125.table
  base := (26200172975951488722201029718108698698113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-134573543757373997789545880770818852000000000000000)
      constant := (4694581338739189491691625724312375671269486414663280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555785055032449511901/100000000000000000000)
  centralHi := (277892527516224755951/50000000000000000000)
  directionLo := (558021623646503119153/100000000000000000000)
  directionHi := (279010811823251559577/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree126.table
  base := (4189038737256545970088116622427467886423/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-22596636730450213066028577648671100000000000000000)
      constant := (794310754569300354703983586267611672691538556284672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree126.table
  base := (134049239407024622273238650630352452620023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-45204690012744245564325001134436800000000000000000)
      constant := (1589409758678488727680630753076980660638624295422192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558021623646503119153/100000000000000000000)
  centralHi := (279010811823251559577/50000000000000000000)
  directionLo := (112049852747201092539/20000000000000000000)
  directionHi := (70031157967000682837/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree127.table
  base := (137129227065504732588226227592128606922829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-68310037420448534608939962764198424000000000000000)
      constant := (2420024096037497305410781314486352793200283886354424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree127.table
  base := (34282306724657772947679967772859899926041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-136654596319091475596404126035801948000000000000000)
      constant := (4842449996486256353968332737347549464009958987698368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112049852747201092539/20000000000000000000)
  centralHi := (70031157967000682837/12500000000000000000)
  directionLo := (281234040692264368253/50000000000000000000)
  directionHi := (562468081384528736507/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree128.table
  base := (14024082744183680237307785415023718334139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3398440560000000000000000000000000000000000000000
      center := (21061243827)
      previous := (0)
      next := (18700510725)
      square := (490976966723343127130330114136912000000000000000)
      linear := (-68830164649546430019794192582383548000000000000000)
      constant := (2457402175924052710697412553764394573748753610277840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree128.table
  base := (2191262926429262773716011810395592611789/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 6796881120000000000000000000000000000000000000000
      center := (42133494429)
      previous := (0)
      next := (37390014675)
      square := (981953933446686254260660228273824000000000000000)
      linear := (-137695122599950214499833248668293496000000000000000)
      constant := (4917243500048668942303080356263414740187392918551552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell143.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281234040692264368253/50000000000000000000)
  centralHi := (562468081384528736507/100000000000000000000)
  directionLo := (35292386286964477181/6250000000000000000)
  directionHi := (564678180591431634897/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 47837
  qDenominator := 90312
  table := BinomialMassData.Q47837_90312.Degree129.table
  base := (143384040664614322622983067195887223496177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1132813520000000000000000000000000000000000000000
      center := (7020414609)
      previous := (0)
      next := (6233503575)
      square := (163658988907781042376776704712304000000000000000)
      linear := (-23116763959548108476882807466856224000000000000000)
      constant := (831688834449445014470416040419093241767173097391304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q47837_90312.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 95699
  qDenominator := 180624
  table := BinomialMassData.Q95699_180624.Degree129.table
  base := (14338404052913466722280768800620867243723/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2265627040000000000000000000000000000000000000000
      center := (14044498143)
      previous := (0)
      next := (12463338225)
      square := (327317977815562084753553409424608000000000000000)
      linear := (-46245216293602984467754123766928348000000000000000)
      constant := (1664203262228119751110436530377462078990629099069920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95699_180624.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell143.Kernel129
