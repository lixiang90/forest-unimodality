import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell303.Parameters
import ForestUnimodality.BinomialMassData.Q63_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q63_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q63_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q129_209.Batch000_049
import ForestUnimodality.BinomialMassData.Q129_209.Batch050_099
import ForestUnimodality.BinomialMassData.Q129_209.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree000.table
  base := (19370123105765661531965093783/1000000000000000000000000000)
  polynomial :=
    { denominator := 20600000000000000000000000000000000000000
      center := (63)
      previous := (0)
      next := (40)
      square := (232739299662008416666458811000000000000)
      linear := (-742930721565417132024045089600000000000)
      constant := (399024535978772627558480931929800000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree000.table
  base := (19370123105765661531965093783/1000000000000000000000000000)
  polynomial :=
    { denominator := 41800000000000000000000000000000000000000
      center := (129)
      previous := (0)
      next := (80)
      square := (472257413877279214400872733000000000000)
      linear := (-1507500202011380394107042948800000000000)
      constant := (809671145821004652036140920129400000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree001.table
  base := (40434025519536249007732703063292598767909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-2646175401966275627461261360370000000000000)
      constant := (859323478651334816682832979909387360657493162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree001.table
  base := (32289227611824895693830820606735718815507/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-4369099550007165396837971414132000000000000)
      constant := (1412746447415987413788461630333944933580161267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48606411862967633061/100000000000000000000)
  directionHi := (24303205931483816531/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree002.table
  base := (135142226435965677049089117286032579976067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-6758608391803204279921213230040000000000000)
      constant := (1440198018135815221776118851722599640966094803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree002.table
  base := (1052037255904642609628663492585088003301/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-13968809194526364424980557663180000000000000)
      constant := (2954542104746592451516522728346450660620222784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/100000000000000000000)
  centralHi := (24303205931483816531/50000000000000000000)
  directionLo := (8592480859362665481/12500000000000000000)
  directionHi := (68739846874901323849/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree003.table
  base := (2825176945363180438526558952218246772911/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-822486597967385730491990373934000000000000)
      constant := (120994855109739720135956485839390520055251196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree003.table
  base := (112406923543338994394140866505373882081663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-34029739028069630715732373582060000000000000)
      constant := (4956137894152636717259214621203166543209121503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8592480859362665481/12500000000000000000)
  centralHi := (68739846874901323849/100000000000000000000)
  directionLo := (84188774920278546287/100000000000000000000)
  directionHi := (5261798432517409143/6250000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree004.table
  base := (94561968407869821911675957967683755272043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-9691123567544510329918594248640000000000000)
      constant := (1019743547253988100646796895690516959681104187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree004.table
  base := (46948148349561773102579366855321238439311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-20060929833543266290751815918880000000000000)
      constant := (2085229654393933189091328977933607016267543791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/100000000000000000000)
  centralHi := (5261798432517409143/6250000000000000000)
  directionLo := (48606411862967633061/50000000000000000000)
  directionHi := (97212823725935266123/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree005.table
  base := (79164857751292369352377444615257899013531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-11157381155415163354917284757940000000000000)
      constant := (862771599315573728979881784900721050634550379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree005.table
  base := (19617982261541259725878145916946536190241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-23106990153051717223637445046730000000000000)
      constant := (1761675909794542558392109526593808294651834242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/50000000000000000000)
  centralHi := (97212823725935266123/100000000000000000000)
  directionLo := (6792952566746738769/6250000000000000000)
  directionHi := (21737448213589564061/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree006.table
  base := (33147845280745846467547602004635763167391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-6311819371642908189957987633620000000000000)
      constant := (366757720390795394209453886431600811442851119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree006.table
  base := (65602483848807049682241151107493206218039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-52306100945120336313046148349160000000000000)
      constant := (2991606106606084728433022884935570740810161559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/6250000000000000000)
  centralHi := (21737448213589564061/20000000000000000000)
  directionLo := (3720653352869806377/3125000000000000000)
  directionHi := (23812181458366760813/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree007.table
  base := (27762264589578456660655672484340821972661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-7044948165578234702457332888270000000000000)
      constant := (313706931512205080030769276019136780307960549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree007.table
  base := (54849549084264356594574918293319011418019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-58398221584137238178817406604860000000000000)
      constant := (2556071894271583933272230146865437737750487939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3720653352869806377/3125000000000000000)
  centralHi := (23812181458366760813/20000000000000000000)
  directionLo := (64300238956296042183/50000000000000000000)
  directionHi := (128600477912592084367/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree008.table
  base := (23248036553668163415762077407538246405019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-7778076959513561214956678142920000000000000)
      constant := (270348741535935609785970226310333256110846571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree008.table
  base := (9170301834944029736180663346440359068599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-12898068444630828008917732972112000000000000)
      constant := (440190690506193322355018319326357324475472919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64300238956296042183/50000000000000000000)
  centralHi := (128600477912592084367/100000000000000000000)
  directionLo := (8592480859362665481/6250000000000000000)
  directionHi := (137479693749802647697/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree009.table
  base := (778331458161742343033208793523941070009/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2121800000000000000000000000000000000000000
      center := (6489)
      previous := (0)
      next := (4120)
      square := (23972147865186866916645257533000000000000)
      linear := (-340448230137955509098240935902800000000000)
      constant := (9404998262736772573482219216391690811725481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree009.table
  base := (9577488596438522697100957398694858553213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-35291231431085520955179961558130000000000000)
      constant := (956607972887509052065583438305625232925794106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8592480859362665481/6250000000000000000)
  centralHi := (137479693749802647697/100000000000000000000)
  directionLo := (145819235588902899183/100000000000000000000)
  directionHi := (9113702224306431199/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree010.table
  base := (32543008321807010941989278537834403721663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-18488669094768428479910737304440000000000000)
      constant := (413492951285191869506844735595285189083122767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree010.table
  base := (31978466910850347384492823951883749203997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-76674583501187943776131181371960000000000000)
      constant := (1682095597797320198441670316824834048979792957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145819235588902899183/100000000000000000000)
  centralHi := (9113702224306431199/6250000000000000000)
  directionLo := (38426742593801460623/25000000000000000000)
  directionHi := (153706970375205842493/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree011.table
  base := (6793544358939619128334408135502242815737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-9977463341319540752454713906870000000000000)
      constant := (184146023212349234189852503851731588064307666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree011.table
  base := (213227249068953537323298266816898342403/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1588400000000000000000000000000000000000000
      center := (4902)
      previous := (0)
      next := (3040)
      square := (17945781727336610147233163854000000000000)
      linear := (-300969833237108529606917962282400000000000)
      constant := (5449807937575830036480538184213916588411565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38426742593801460623/25000000000000000000)
  centralHi := (153706970375205842493/100000000000000000000)
  directionLo := (8060461527747162311/5000000000000000000)
  directionHi := (161209230554943246221/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree012.table
  base := (22643366677131397349945587993087812080147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-21421184270509734529908118323040000000000000)
      constant := (332878534261415899176994852747148598358279523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree012.table
  base := (35466149863250920855992007331055856059/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17472400000000000000000000000000000000000000
      center := (53922)
      previous := (0)
      next := (33440)
      square := (197403599000702711619564802394000000000000)
      linear := (-3554352991168869900306947915334400000000000)
      constant := (54226543216004391749696812981677071212829475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8060461527747162311/5000000000000000000)
  centralHi := (161209230554943246221/100000000000000000000)
  directionLo := (84188774920278546287/50000000000000000000)
  directionHi := (6735101993622283703/4000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree013.table
  base := (4703080414352460628453365952955539339561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-11443720929190193777453404416170000000000000)
      constant := (152892836993789325288737827078295633706805298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree013.table
  base := (18377853081319449304768164124352491653743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-94950945418238649373444956139060000000000000)
      constant := (1246904504946466425901805884431371187927147983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/50000000000000000000)
  centralHi := (6735101993622283703/4000000000000000000)
  directionLo := (43813227572062732337/25000000000000000000)
  directionHi := (175252910288250929349/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree014.table
  base := (3113257360470528877877259225620744316397/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-4870739889250208115981099868328000000000000)
      constant := (57159204743212435069544960046762476452655773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree014.table
  base := (15172410436748539530868637075121695850547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-101043066057255551239216214394760000000000000)
      constant := (1167373754933315597118419521381630796447743507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43813227572062732337/25000000000000000000)
  centralHi := (175252910288250929349/100000000000000000000)
  directionLo := (181868539991649377867/100000000000000000000)
  directionHi := (45467134997912344467/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree015.table
  base := (12809922732824531716529704610885680143663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-25819957034121693604904189850940000000000000)
      constant := (271898127973620380688976650046736180644120767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree015.table
  base := (389193911807753333073367208108577806673/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-53567593348136226552493736325230000000000000)
      constant := (556443114798165756321274129959577594772533008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181868539991649377867/100000000000000000000)
  centralHi := (45467134997912344467/25000000000000000000)
  directionLo := (188251823664172267531/100000000000000000000)
  directionHi := (47062955916043066883/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree016.table
  base := (10463944517557126969270320710674062836613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-27286214621992346629902880360240000000000000)
      constant := (263250852924427049428179736653781132633627317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree016.table
  base := (2535924322168665111757543098619455455737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-56613653667644677485379365453080000000000000)
      constant := (539983770749543287646546700928472867524095794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188251823664172267531/100000000000000000000)
  centralHi := (47062955916043066883/25000000000000000000)
  directionLo := (48606411862967633061/25000000000000000000)
  directionHi := (38885129490374106449/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree017.table
  base := (8462352080318775210215870252202334582829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-28752472209862999654901570869540000000000000)
      constant := (259154003759740554334539423329544567589232861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree017.table
  base := (12773103463403659102861471788976247471/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (134805)
      previous := (0)
      next := (83600)
      square := (493508997501756779048912005985000000000000)
      linear := (-11931942797430625683652998916186000000000000)
      constant := (106573035240128229098601026719370373809968064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/25000000000000000000)
  centralHi := (38885129490374106449/20000000000000000000)
  directionLo := (200409370193290840143/100000000000000000000)
  directionHi := (12525585637080677509/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree018.table
  base := (3375073588748611838663795415332445551959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-15109364898866826339950130689420000000000000)
      constant := (129512052056539252927793239860721914860733031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree018.table
  base := (6492481524925646272634388903516626613519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-125411548613323158702301247417560000000000000)
      constant := (1067772625040330548690711839665589767105123439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200409370193290840143/100000000000000000000)
  centralHi := (12525585637080677509/6250000000000000000)
  directionLo := (25777442578087996443/12500000000000000000)
  directionHi := (41243908124940794309/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree019.table
  base := (660181292071238083631748946710636941069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-15842493692802152852449475944070000000000000)
      constant := (131187209330224491622780569582217589231204084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree019.table
  base := (5050985172591928870931686119526518969169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (70950)
      previous := (0)
      next := (44000)
      square := (259741577632503567920480003150000000000000)
      linear := (-6921245750123161082530131877540000000000000)
      constant := (57057571325361354411012024089701467110119531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25777442578087996443/12500000000000000000)
  centralHi := (41243908124940794309/20000000000000000000)
  directionLo := (211870437318792477957/100000000000000000000)
  directionHi := (105935218659396238979/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree020.table
  base := (502243337426728328019073171762212644461/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-16575622486737479364948821198720000000000000)
      constant := (134399232536012584515620927969301255780346996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree020.table
  base := (152484465848899075442952126933554718831/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17472400000000000000000000000000000000000000
      center := (53922)
      previous := (0)
      next := (33440)
      square := (197403599000702711619564802394000000000000)
      linear := (-5503831595654278497353750557158400000000000)
      constant := (44521042456681625575173534045992603673256911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211870437318792477957/100000000000000000000)
  centralHi := (105935218659396238979/50000000000000000000)
  directionLo := (6792952566746738769/3125000000000000000)
  directionHi := (217374482135895640609/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree021.table
  base := (1463801230486723519060025097129187975901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-17308751280672805877448166453370000000000000)
      constant := (138978198354986406391176443273288555236333709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree021.table
  base := (109759420947763523278767816694177290121/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17472400000000000000000000000000000000000000
      center := (53922)
      previous := (0)
      next := (33440)
      square := (197403599000702711619564802394000000000000)
      linear := (-5747516421214954571984600887386400000000000)
      constant := (46127075737283666741053070330010758209775401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/3125000000000000000)
  centralHi := (217374482135895640609/100000000000000000000)
  directionLo := (22274256162224868701/10000000000000000000)
  directionHi := (222742561622248687011/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree022.table
  base := (1983604039943801472920729975766316114291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-36083760149216264779895023416040000000000000)
      constant := (289563748290227546775773955864784847656513219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree022.table
  base := (909983484006100051249672840985596339241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19855000000000000000000000000000000000000000
      center := (61275)
      previous := (0)
      next := (38000)
      square := (224322271591707626840414548175000000000000)
      linear := (-6808183234972307552972103656380000000000000)
      constant := (54699213477602697407844578660013803063126011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22274256162224868701/10000000000000000000)
  centralHi := (222742561622248687011/100000000000000000000)
  directionLo := (113992140115265945343/50000000000000000000)
  directionHi := (227984280230531890687/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree023.table
  base := (46539227196282598106632774176276582771/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (12978)
      previous := (0)
      next := (8240)
      square := (47944295730373733833290515066000000000000)
      linear := (-1502000709483476712195748557013600000000000)
      constant := (12135285102318106633692029111370918266617539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree023.table
  base := (508882291974141218507944721302530213989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-77936075904203834015578769348030000000000000)
      constant := (631334880103783110741234528580780822277253509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113992140115265945343/50000000000000000000)
  centralHi := (227984280230531890687/100000000000000000000)
  directionLo := (1165540811237707529/500000000000000000)
  directionHi := (233108162247541505801/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree024.table
  base := (448378197917838017497173968601077301293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-39016275324957570829892404434640000000000000)
      constant := (319211510486280427112298148773048829089417437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree024.table
  base := (318702378211084467851631604403352792491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-161964272447424569896928796951760000000000000)
      constant := (1330222298470057185825670989235782853328799371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1165540811237707529/500000000000000000)
  centralHi := (233108162247541505801/100000000000000000000)
  directionLo := (3720653352869806377/1562500000000000000)
  directionHi := (238121814583667608129/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree025.table
  base := (-22192830963626852112298486937532986823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-20241266456414111927445547471970000000000000)
      constant := (168441929280086614116343837014443850171179172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree025.table
  base := (-292886455314397858924657607742627970709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-168056393086441471762700055207460000000000000)
      constant := (1405355969536822743922416478936444267611460171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3720653352869806377/1562500000000000000)
  centralHi := (238121814583667608129/100000000000000000000)
  directionLo := (48606411862967633061/20000000000000000000)
  directionHi := (121516029657419082653/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree026.table
  base := (-145520995784870765683675038762364630169/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-8389758100139775375977957090648000000000000)
      constant := (71251565355770878503050926207698073638537079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree026.table
  base := (-830161308216375955663577043356503336427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-174148513725458373628471313463160000000000000)
      constant := (1487495958023898233069819017917504577761532213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48606411862967633061/20000000000000000000)
  centralHi := (121516029657419082653/50000000000000000000)
  directionLo := (12392252128749989333/5000000000000000000)
  directionHi := (247845042574999786661/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree027.table
  base := (-606514872671516325784607978214327236471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-21707524044284764952444237981270000000000000)
      constant := (188607186043929968875760162415289202348279161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree027.table
  base := (-652094931332718288470214863888714647477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-90120317182237637747121285859430000000000000)
      constant := (788079408253195126620637397364562055483557163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12392252128749989333/5000000000000000000)
  centralHi := (247845042574999786661/100000000000000000000)
  directionLo := (252566324760835638861/100000000000000000000)
  directionHi := (126283162380417819431/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree028.table
  base := (-410819889155163265746442891264575596911/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-22440652838220091464943583235920000000000000)
      constant := (199826552830676792346582755503308234984742402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree028.table
  base := (-862146410239008960822525197311657169339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-93166377501746088680006914987280000000000000)
      constant := (835468703704127483735538469186069503186103141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252566324760835638861/100000000000000000000)
  centralHi := (126283162380417819431/50000000000000000000)
  directionLo := (257200955825184168733/100000000000000000000)
  directionHi := (128600477912592084367/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree029.table
  base := (-1013172275260378789148369617205894957561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-23173781632155417977442928490570000000000000)
      constant := (211744630063900955395942670407867660395235351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree029.table
  base := (-2098330057680120608090930802341179248103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-192424875642509079225785088230260000000000000)
      constant := (1771488403484800642750673815345824949263612857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200955825184168733/100000000000000000000)
  centralHi := (128600477912592084367/50000000000000000000)
  directionLo := (261753538565538362481/100000000000000000000)
  directionHi := (130876769282769181241/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree030.table
  base := (-592245076340538638916036541994384747373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-23906910426090744489942273745220000000000000)
      constant := (224325582778410339087969433828063144430239686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree030.table
  base := (-2432938401316140139428946300681206744919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-198516996281525981091556346485960000000000000)
      constant := (1877521901493901039106932039497744208175193161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261753538565538362481/100000000000000000000)
  centralHi := (130876769282769181241/50000000000000000000)
  directionLo := (16639267635458798599/6250000000000000000)
  directionHi := (53245656433468155517/20000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree031.table
  base := (-1338453022911021621186533741805228514279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-24640039220026071002441618999870000000000000)
      constant := (237539073346904740015439364801233330692014089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree031.table
  base := (-546745883474455726627256173119616954633/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-40921823384108576591465520948332000000000000)
      constant := (397758556524342572369266147514844011804675927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16639267635458798599/6250000000000000000)
  centralHi := (53245656433468155517/20000000000000000000)
  directionLo := (270629047775669602319/100000000000000000000)
  directionHi := (3382863097195870029/1250000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree032.table
  base := (-2954969944836321907383652142196121789519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-50746336027922795029881928509040000000000000)
      constant := (502718769272091371621306706328721343934992929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree032.table
  base := (-3005454115644250483653704730112790608567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-210701237559559784823098862997360000000000000)
      constant := (2105093518009349510505302625026663193427184873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270629047775669602319/100000000000000000000)
  centralHi := (3382863097195870029/1250000000000000000)
  directionLo := (274959387499605295393/100000000000000000000)
  directionHi := (137479693749802647697/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree033.table
  base := (-3207287135220218202820311532954722854597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-52212593615793448054880619018340000000000000)
      constant := (531529375847629602785834917406653345235580427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree033.table
  base := (-650428052051390107288872717871345557859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7942000000000000000000000000000000000000000
      center := (24510)
      previous := (0)
      next := (15200)
      square := (89728908636683050736165819270000000000000)
      linear := (-3941697421792303394343093113692000000000000)
      constant := (40477239470764935515257673359018886789741911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274959387499605295393/100000000000000000000)
  centralHi := (137479693749802647697/50000000000000000000)
  directionLo := (11168903118809871129/4000000000000000000)
  directionHi := (139611288985123389113/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree034.table
  base := (-3437355066465308351300673199338892221939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-53678851203664101079879309527640000000000000)
      constant := (561472861978768041378712952227773692417449149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree034.table
  base := (-3477206975177246769182734944862063297659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-222885478837593588554641379508760000000000000)
      constant := (2352107390515881930215140114987920213094957221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11168903118809871129/4000000000000000000)
  centralHi := (139611288985123389113/50000000000000000000)
  directionLo := (141710824677001105647/50000000000000000000)
  directionHi := (56684329870800442259/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree035.table
  base := (-3648150037133862328863480127916951600117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-55145108791534754104878000036940000000000000)
      constant := (592517652114059565224145786447579060474358747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree035.table
  base := (-46044506413397392094949647044147146169/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (134805)
      previous := (0)
      next := (83600)
      square := (493508997501756779048912005985000000000000)
      linear := (-22897759947661049042041263776446000000000000)
      constant := (248254422885804890700845909700501868065535288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141710824677001105647/50000000000000000000)
  centralHi := (56684329870800442259/20000000000000000000)
  directionLo := (287559410551516158729/100000000000000000000)
  directionHi := (28755941055151615873/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree036.table
  base := (-1921104035189526283166646634703120744583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-28305683189702703564938345273120000000000000)
      constant := (312318420791936084001757826469954592020718953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree036.table
  base := (-1936837190522882786308977781396368476797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-117534860057813696143091948010080000000000000)
      constant := (1308725320327355480966948051117305228565030243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287559410551516158729/100000000000000000000)
  centralHi := (28755941055151615873/10000000000000000000)
  directionLo := (291638471177805798367/100000000000000000000)
  directionHi := (9113702224306431199/3125000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree037.table
  base := (-4021692753971100705379311991770663350077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-58077623967276060154875381055540000000000000)
      constant := (657807476885551568320354015610035032519033107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree037.table
  base := (-2024828230906233217829946810014313012817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-120580920377322147075977577137930000000000000)
      constant := (1378367275740534283244379092796649793287140623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291638471177805798367/100000000000000000000)
  centralHi := (9113702224306431199/3125000000000000000)
  directionLo := (9239414400384450063/3125000000000000000)
  directionHi := (295661260812302402017/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree038.table
  base := (-65444565874728690616264421745502899631/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-29771940777573356589937035782420000000000000)
      constant := (346004975614187620151561210496322711610071072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree038.table
  base := (-4213305312132546460837445744869334377237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (70950)
      previous := (0)
      next := (44000)
      square := (259741577632503567920480003150000000000000)
      linear := (-13013366389140062948301390133240000000000000)
      constant := (152648284135750508349514168996665400266732137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9239414400384450063/3125000000000000000)
  centralHi := (295661260812302402017/100000000000000000000)
  directionLo := (299630045922155050941/100000000000000000000)
  directionHi := (149815022961077525471/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree039.table
  base := (-4344067035906275109913910185745786081429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-61010139143017366204872762074140000000000000)
      constant := (727227496244506020156472997517432955462119739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree039.table
  base := (-4366157444283280817233579310902819982723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-253346082032678097883497670787260000000000000)
      constant := (3048132065556500581729216080418943920334676637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299630045922155050941/100000000000000000000)
  centralHi := (149815022961077525471/50000000000000000000)
  directionLo := (75886736198390256521/25000000000000000000)
  directionHi := (60709388958712205217/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree040.table
  base := (-2244945292218611427518310956048059352923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-31238198365444009614935726291720000000000000)
      constant := (381722877012119236799157553832086138324839893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree040.table
  base := (-901905417285653111927710915748578101059/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-51887640534338999949853785808592000000000000)
      constant := (640024229122475459296961087119266359967641821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75886736198390256521/25000000000000000000)
  centralHi := (60709388958712205217/20000000000000000000)
  directionLo := (61482788150082336997/20000000000000000000)
  directionHi := (153706970375205842493/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree041.table
  base := (-4627083031960608154907306467441169028469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-63942654318758672254870143092740000000000000)
      constant := (800652416319956770037126435253406637776972379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree041.table
  base := (-4644539662226663456323045215676884320987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-265530323310711901615040187298660000000000000)
      constant := (3356235479116033914026705980008028015974966853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61482788150082336997/20000000000000000000)
  centralHi := (153706970375205842493/50000000000000000000)
  directionLo := (31123289389441159553/10000000000000000000)
  directionHi := (311232893894411595531/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree042.table
  base := (-297290003531473734133661020649797907563/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-32704455953314662639934416801020000000000000)
      constant := (419418459991735444263091887249750351989313064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree042.table
  base := (-4772160019156508742968028732769169783077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-271622443949728803480811445554360000000000000)
      constant := (3516432920564782420906136934993229894705413563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31123289389441159553/10000000000000000000)
  centralHi := (311232893894411595531/100000000000000000000)
  directionLo := (63001110312781792201/20000000000000000000)
  directionHi := (157502775781954480503/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree043.table
  base := (-4879417108799755607226299887856791342533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-66875169494499978304867524111340000000000000)
      constant := (877990189537947875931624457685897300647067403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree043.table
  base := (-4893216260885120999852584814237304070403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-277714564588745705346582703810060000000000000)
      constant := (3680677297562330630536927820865630320900726557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63001110312781792201/20000000000000000000)
  centralHi := (157502775781954480503/50000000000000000000)
  directionLo := (318733557678313734091/100000000000000000000)
  directionHi := (79683389419578433523/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree044.table
  base := (-199845997952216701354983346118115352679/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4243600000000000000000000000000000000000000
      center := (12978)
      previous := (0)
      next := (8240)
      square := (47944295730373733833290515066000000000000)
      linear := (-2733657083294825253194648584825600000000000)
      constant := (36724176772240461547312944752591314223428489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree044.table
  base := (-5008419895088250814040492376952106540889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (122550)
      previous := (0)
      next := (76000)
      square := (448644543183415253680829096350000000000000)
      linear := (-25800607747978418837486723824160000000000000)
      constant := (349903411885626734684140519159763184926129781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318733557678313734091/100000000000000000000)
  centralHi := (79683389419578433523/25000000000000000000)
  directionLo := (322418461109886492441/100000000000000000000)
  directionHi := (161209230554943246221/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree045.table
  base := (-638434006159247191286282847312014489639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-34903842335120642177432452564970000000000000)
      constant := (479586444387610464413575471874992353117679396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree045.table
  base := (-5118382889055642519059604702251071384273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-289898805866779509078125220321460000000000000)
      constant := (4021186888760289451639160445486420950863571087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322418461109886492441/100000000000000000000)
  centralHi := (161209230554943246221/50000000000000000000)
  directionLo := (20378857700240216307/6250000000000000000)
  directionHi := (326061723203843460913/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree046.table
  base := (-2606964681769439457610097633397664764889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-35636971129055968689931797819620000000000000)
      constant := (500594902963330773098010507972504174509292599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree046.table
  base := (-2611816063419955792412594348208495339647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-147995463252898205471948239288580000000000000)
      constant := (2098701178397607222268201625659684715068879393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20378857700240216307/6250000000000000000)
  centralHi := (326061723203843460913/100000000000000000000)
  directionLo := (32966472455034109983/10000000000000000000)
  directionHi := (329664724550341099831/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree047.table
  base := (-2657996436469715337483821117419023190659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-36370099922991295202431143074270000000000000)
      constant := (522075087059652330876871269104866582970298669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree047.table
  base := (-1331155420002068245103864536214235319477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-151041523572406656404833868416430000000000000)
      constant := (2188782050273270771576484335947936974019850326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32966472455034109983/10000000000000000000)
  centralHi := (329664724550341099831/100000000000000000000)
  directionLo := (166614385548670969579/50000000000000000000)
  directionHi := (333228771097341939159/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree048.table
  base := (-676758657679934829407217001358636645557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-37103228716926621714930488328920000000000000)
      constant := (544024839421488917567598790836904895309143148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree048.table
  base := (-2710871618142848349640356101566000939723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-154087583891915107337719497544280000000000000)
      constant := (2280827505351378166602477094900935512951959637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166614385548670969579/50000000000000000000)
  centralHi := (333228771097341939159/100000000000000000000)
  directionLo := (84188774920278546287/25000000000000000000)
  directionHi := (336755099681114185149/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree049.table
  base := (-1101702001707941671034049545569088499471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-15134543004344779290971933433428000000000000)
      constant := (226576918250331658648821770877539540109112161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree049.table
  base := (-5515334974103122450513046254358290268329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-314267288422847116541210253344260000000000000)
      constant := (4749660315291816937259507986607465522789120951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84188774920278546287/25000000000000000000)
  centralHi := (336755099681114185149/100000000000000000000)
  directionLo := (85061220760193357857/25000000000000000000)
  directionHi := (340244883040773431429/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree050.table
  base := (-5599619144597323175592323611383884615269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-77138972609594549479858357676440000000000000)
      constant := (1178651685887286465837004622043828368116611179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree050.table
  base := (-2802844562143379798040081298935890457149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-160179704530932009203490755799980000000000000)
      constant := (2470783624689501852088259429087681368941274531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85061220760193357857/25000000000000000000)
  centralHi := (340244883040773431429/100000000000000000000)
  directionLo := (343699234374506619241/100000000000000000000)
  directionHi := (171849617187253309621/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree051.table
  base := (-11108710690459457633374477369635863943/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-39302615098732601252428524092870000000000000)
      constant := (612674085209828141498141530977341478573750528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree051.table
  base := (-5693058421199586504433885272174571589453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-326451529700880920272752769855660000000000000)
      constant := (5137364773274607375843642678679752538401103507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343699234374506619241/100000000000000000000)
  centralHi := (171849617187253309621/50000000000000000000)
  directionLo := (347119211487659485769/100000000000000000000)
  directionHi := (34711921148765948577/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree052.table
  base := (-1443215058776317608573012099303411825867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-40035743892667927764927869347520000000000000)
      constant := (636485812787202154430418883378020207878753994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree052.table
  base := (-5777661613219763327469240996962452459391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-332543650339897822138524028111360000000000000)
      constant := (5337043331830721538665952785977603114121341729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (347119211487659485769/100000000000000000000)
  centralHi := (34711921148765948577/10000000000000000000)
  directionLo := (350505820576501858697/100000000000000000000)
  directionHi := (175252910288250929349/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree053.table
  base := (-5855417952158747005857844818008884305039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-81537745373206508554854429204340000000000000)
      constant := (1321519953710437223181721186788313746407841249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree053.table
  base := (-5859688175397018026075543698389687041393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-338635770978914724004295286367060000000000000)
      constant := (5540594648587699025583843058460570080344912367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350505820576501858697/100000000000000000000)
  centralHi := (175252910288250929349/50000000000000000000)
  directionLo := (70772003937206512991/20000000000000000000)
  directionHi := (88465004921508141239/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree054.table
  base := (-2967752292229829841369421522997992355013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-41502001480538580789926559856820000000000000)
      constant := (685495667375003350438303046016694299105667083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree054.table
  base := (-296965117227359234146725159562651042469/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (134805)
      previous := (0)
      next := (83600)
      square := (493508997501756779048912005985000000000000)
      linear := (-34472789161793162587006654462276000000000000)
      constant := (574801154951718738803169372970851679627823222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70772003937206512991/20000000000000000000)
  centralHi := (88465004921508141239/25000000000000000000)
  directionLo := (357182721875501412193/100000000000000000000)
  directionHi := (178591360937750706097/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree055.table
  base := (-1202653818578695669910280465470917512717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-16894052109789562920970362044588000000000000)
      constant := (284276837673415758387919505449709036107585347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree055.table
  base := (-1203329315633573422577399395442345961029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7942000000000000000000000000000000000000000
      center := (24510)
      previous := (0)
      next := (15200)
      square := (89728908636683050736165819270000000000000)
      linear := (-6378545677399064140651596415972000000000000)
      constant := (108350687489695159886789825992208444188753841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357182721875501412193/100000000000000000000)
  centralHi := (178591360937750706097/50000000000000000000)
  directionLo := (360474798121289244323/100000000000000000000)
  directionHi := (90118699530322311081/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree056.table
  base := (-6088840900815105119985819686973884210251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-85936518136818467629850500732240000000000000)
      constant := (1472697141509281339846555131296734062413447141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree056.table
  base := (-1522961130689456615415960058194545285849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-178456066447982714800804530567080000000000000)
      constant := (3087209017416562928601207710162088134737659662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360474798121289244323/100000000000000000000)
  centralHi := (90118699530322311081/25000000000000000000)
  directionLo := (72747415996659751147/20000000000000000000)
  directionHi := (45467134997912344467/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree057.table
  base := (-6162332526424099822371629006982226302093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-87402775724689120654849191241540000000000000)
      constant := (1524929000471035214378730879222455561161095363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree057.table
  base := (-3082501781940548810830133546382975300303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11495000000000000000000000000000000000000000
      center := (35475)
      previous := (0)
      next := (22000)
      square := (129870788816251783960240001575000000000000)
      linear := (-9552743514078482407036324194470000000000000)
      constant := (168247303355474762373260591571680539784603403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72747415996659751147/20000000000000000000)
  centralHi := (45467134997912344467/12500000000000000000)
  directionLo := (366970362057985708671/100000000000000000000)
  directionHi := (2866955953578013349/781250000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree058.table
  base := (-1558460462156567395442199661027105460057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-44434516656279886839923940875420000000000000)
      constant := (789039363427514353873181783364586876348510574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree058.table
  base := (-779527127400690081142883196818445341373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-184548187086999616666575788822780000000000000)
      constant := (3308111106874465105610056020191833956173943948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366970362057985708671/100000000000000000000)
  centralHi := (2866955953578013349/781250000000000000)
  directionLo := (370175404238533327297/100000000000000000000)
  directionHi := (185087702119266663649/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree059.table
  base := (-1575863514845646490015385473924831445151/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-45167645450215213352423286130070000000000000)
      constant := (816072708429873936324711787472667926396786082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree059.table
  base := (-3152783013204788782584736437623449237873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-187594247406508067599461417950630000000000000)
      constant := (3421444274690429903574621462148015113840469487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370175404238533327297/100000000000000000000)
  centralHi := (185087702119266663649/50000000000000000000)
  directionLo := (14934117352015364329/4000000000000000000)
  directionHi := (186676466900192054113/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree060.table
  base := (-3185621673782227053661619151212317631099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-45900774244150539864922631384720000000000000)
      constant := (843564141707727985925391210161988522251670709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree060.table
  base := (-3186560584998593177990812990788605327043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-190640307726016518532347047078480000000000000)
      constant := (3536696725601057058207126172872162930709434717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14934117352015364329/4000000000000000000)
  centralHi := (186676466900192054113/50000000000000000000)
  directionLo := (188251823664172267531/50000000000000000000)
  directionHi := (376503647328344535063/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree061.table
  base := (-1609318588150947320843175700788586860623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-46633903038085866377421976639370000000000000)
      constant := (871513320381209908179511147589312763991301186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree061.table
  base := (-6438943884443593330621347481596652717261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-387372736091049938930465352412660000000000000)
      constant := (7307734235693379904989884452259586612657322259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188251823664172267531/50000000000000000000)
  centralHi := (376503647328344535063/100000000000000000000)
  directionLo := (7592564249994566351/2000000000000000000)
  directionHi := (379628212499728317551/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree062.table
  base := (-812700427567953333159577081232757320139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-47367031832021192889921321894020000000000000)
      constant := (899919945562734422990321389053546710362581396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree062.table
  base := (-6503087665514276079055136076612071897601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-393464856730066840796236610668360000000000000)
      constant := (7545908566106125346268812614070028087440890719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7592564249994566351/2000000000000000000)
  centralHi := (379628212499728317551/100000000000000000000)
  directionLo := (191363634868234121509/50000000000000000000)
  directionHi := (382727269736468243019/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree063.table
  base := (-6564279690290725431284855423722980587527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-96200321251913038804841334297340000000000000)
      constant := (1857567513189941252593590939068692898946926057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree063.table
  base := (-6565599116884561261047758027431158150947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-399556977369083742662007868924060000000000000)
      constant := (7787914406745208496425852076137309580808484093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191363634868234121509/50000000000000000000)
  centralHi := (382727269736468243019/100000000000000000000)
  directionLo := (385801433737776253099/100000000000000000000)
  directionHi := (3858014337377762531/1000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree064.table
  base := (-331267301690236544282466508602272895753/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-9766657883978369182984002480664000000000000)
      constant := (191620905212721715916505825376252973697912846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree064.table
  base := (-6626518855200476371310813399286470370807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-405649098008100644527779127179760000000000000)
      constant := (8033749983434914228464505436012007687732779433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385801433737776253099/100000000000000000000)
  centralHi := (3858014337377762531/1000000000000000000)
  directionLo := (388851294903741064489/100000000000000000000)
  directionHi := (38885129490374106449/10000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree065.table
  base := (-3342419935255632063456367409421064018327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-49566418213827172427419357657970000000000000)
      constant := (987882055477305075730302641174376931829568857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree065.table
  base := (-1671470573336145308007174767990903083289/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-205870609323558773196775192717730000000000000)
      constant := (4141706874652559723395968026794103724837706382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388851294903741064489/100000000000000000000)
  centralHi := (38885129490374106449/10000000000000000000)
  directionLo := (78375484131840268257/20000000000000000000)
  directionHi := (195938710329600670643/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree066.table
  base := (-6742793873300585908052876959267898964941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-100599094015524997879837405825240000000000000)
      constant := (2036232343045427453151890464050366859880940931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree066.table
  base := (-1348744063761384282874861735913746585181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7942000000000000000000000000000000000000000
      center := (24510)
      previous := (0)
      next := (15200)
      square := (89728908636683050736165819270000000000000)
      linear := (-7596969805202444513805848067112000000000000)
      constant := (155216442821079481287522559309718512310246249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78375484131840268257/20000000000000000000)
  centralHi := (195938710329600670643/50000000000000000000)
  directionLo := (394880356686301987607/100000000000000000000)
  directionHi := (49360044585787748451/12500000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree067.table
  base := (-849904572623391198266645986378161458597/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-51032675801697825452418048167270000000000000)
      constant := (1048806722815693370376914034205021340342977708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree067.table
  base := (-3400029940814813755491438861816266108043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-211962729962575675062546450973430000000000000)
      constant := (4397110311896439997056509919704288680134573717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394880356686301987607/100000000000000000000)
  centralHi := (49360044585787748451/12500000000000000000)
  directionLo := (39786062807331605013/10000000000000000000)
  directionHi := (397860628073316050131/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree068.table
  base := (-1713548232497380006076001830700817163141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-51765804595633151964917393421920000000000000)
      constant := (1079953577081011411546627752459150061432474262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree068.table
  base := (-3427462252163095577563888967816847085757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-215008790282084125995432080101280000000000000)
      constant := (4527680763859366594328379567553832302447048483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39786062807331605013/10000000000000000000)
  centralHi := (397860628073316050131/100000000000000000000)
  directionLo := (400818740386581680287/100000000000000000000)
  directionHi := (12525585637080677509/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree069.table
  base := (-3453842358094070237894670639494809826457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-52498933389568478477416738676570000000000000)
      constant := (1111556618702420357118359965101204562551117687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree069.table
  base := (-1727083681104072261978704739047801817313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-218054850601592576928317709229130000000000000)
      constant := (4660163084918767028231977889109950937635901694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400818740386581680287/100000000000000000000)
  centralHi := (12525585637080677509/3125000000000000000)
  directionLo := (16150207226870045573/4000000000000000000)
  directionHi := (201877590335875569663/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree070.table
  base := (-6959730996379607260753749199273898254867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-106464124367007609979832167862440000000000000)
      constant := (2287231493186285111643595320986703213414115997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree070.table
  base := (-3480154239358305840175735103195607884423/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-221100910921101027861203338356980000000000000)
      constant := (4794556883325596370098456248481412652000518937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16150207226870045573/4000000000000000000)
  centralHi := (201877590335875569663/50000000000000000000)
  directionLo := (406670418389967043651/100000000000000000000)
  directionHi := (101667604597491760913/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree071.table
  base := (-109536694334908212197319855947797350757/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-53965190977439131502415429185870000000000000)
      constant := (1176130872343765004165948827662839172986207584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree071.table
  base := (-7010861437247556944369696939976547890281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-448293942481218957588177934969660000000000000)
      constant := (9861723633677548239538149117087694411604635639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406670418389967043651/100000000000000000000)
  centralHi := (101667604597491760913/25000000000000000000)
  directionLo := (409564906294061388661/100000000000000000000)
  directionHi := (204782453147030694331/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree072.table
  base := (-7059551620138544321792172783573738957149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-109396639542748916029829548881040000000000000)
      constant := (2418203837221007724466035657557946203403606259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree072.table
  base := (-7060007293521328174214759861270996598163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-454386063120235859453949193225360000000000000)
      constant := (10138155172770294000644498405768941597595641997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409564906294061388661/100000000000000000000)
  centralHi := (204782453147030694331/50000000000000000000)
  directionLo := (412439081249407943089/100000000000000000000)
  directionHi := (41243908124940794309/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree073.table
  base := (-7107353303746307203193995074730464728967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-110862897130619569054828239390340000000000000)
      constant := (2485057635423798475631677902837554499690389097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree073.table
  base := (-3553879008520358040666584072715395695567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-230239091879626380659860225740530000000000000)
      constant := (5209203930544789311224632697863283800621937873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412439081249407943089/100000000000000000000)
  centralHi := (41243908124940794309/10000000000000000000)
  directionLo := (415293365003641934413/100000000000000000000)
  directionHi := (207646682501820967207/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree074.table
  base := (-7153764656431222008817808503926102552439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-112329154718490222079826929899640000000000000)
      constant := (2552823020812746335048539505319007978021174649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree074.table
  base := (-7154124073035878986832383730709502195287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-466570304398269663185491709736760000000000000)
      constant := (10702481241503683559328155042035718234607668553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415293365003641934413/100000000000000000000)
  centralHi := (207646682501820967207/50000000000000000000)
  directionLo := (104532041227271736477/25000000000000000000)
  directionHi := (418128164909086945909/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree075.table
  base := (-3599397728067310398861954765628646018699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-56897706153180437552412810204470000000000000)
      constant := (1310749944826835855451024889928570694387622309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree075.table
  base := (-1799778653444680394177909089135629352999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-236331212518643282525631483996230000000000000)
      constant := (5495187457116109871346017495224058148463301362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104532041227271736477/25000000000000000000)
  centralHi := (418128164909086945909/100000000000000000000)
  directionLo := (105235968650348182859/25000000000000000000)
  directionHi := (420943874601392731437/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree076.table
  base := (-1448490853137561039683058561140815457353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-23052333978846305625964862183648000000000000)
      constant := (538217630220699464843084091244185088812942023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree076.table
  base := (-90534220565301014230364105488016391891/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2299000000000000000000000000000000000000000
      center := (7095)
      previous := (0)
      next := (4400)
      square := (25974157763250356792048000315000000000000)
      linear := (-2519760766717386667984390664464000000000000)
      constant := (59379413313510915394670755269608402520340728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105235968650348182859/25000000000000000000)
  centralHi := (420943874601392731437/100000000000000000000)
  directionLo := (211870437318792477957/50000000000000000000)
  directionHi := (84748174927516991183/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree077.table
  base := (-7284748585569058363699256889228551733721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-116727927482102181154823001427540000000000000)
      constant := (2761587725589649069020518903966504294656953911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree077.table
  base := (-227656255381860830100881718574409799681/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19855000000000000000000000000000000000000000
      center := (61275)
      previous := (0)
      next := (38000)
      square := (224322271591707626840414548175000000000000)
      linear := (-22038484832514562217400249295630000000000000)
      constant := (526255535524068117084362708359391298967467984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211870437318792477957/50000000000000000000)
  centralHi := (84748174927516991183/20000000000000000000)
  directionLo := (213259766548227475307/50000000000000000000)
  directionHi := (85303906619290990123/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree078.table
  base := (-915710623400573001559045992523728356197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-59097092534986417089910845968420000000000000)
      constant := (1416499271697933175031785726359923063476424108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree078.table
  base := (-1831477081272309321696213123678156303831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-245469393477168635324288371379780000000000000)
      constant := (5938487201170402917113940891915568908984716178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213259766548227475307/50000000000000000000)
  centralHi := (85303906619290990123/20000000000000000000)
  directionLo := (85856041228794231109/20000000000000000000)
  directionHi := (214640103071985577773/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree079.table
  base := (-7365269229335003418977907667255130382617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-119660442657843487204820382446140000000000000)
      constant := (2905320543427669916246131126833700321770816247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree079.table
  base := (-1841366867505244597881049530495774566853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-248515453796677086257174000507630000000000000)
      constant := (6090073078800272656338868405067273142290588214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85856041228794231109/20000000000000000000)
  centralHi := (214640103071985577773/50000000000000000000)
  directionLo := (432023238566171126853/100000000000000000000)
  directionHi := (216011619283085563427/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree080.table
  base := (-231359573738580713725263051027370806351/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-60563350122857070114909536477720000000000000)
      constant := (1489276836067141738429186526436009969846755856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree080.table
  base := (-7403682305362297654435517860478455631671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-503123028232371074380119259270960000000000000)
      constant := (12487136842080198650378876535357240579552979049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432023238566171126853/100000000000000000000)
  centralHi := (216011619283085563427/50000000000000000000)
  directionLo := (6792952566746738769/1562500000000000000)
  directionHi := (434748964271791281217/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree081.table
  base := (-1860100200870397092934003311311858174779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-61296478916792396627408881732370000000000000)
      constant := (1526348941283434503430272829234629993247539178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree081.table
  base := (-3720278472825560770942765285197250227663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-254607574435693988122945258763330000000000000)
      constant := (6398973138026317340676968156483503912805452497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/1562500000000000000)
  centralHi := (434748964271791281217/100000000000000000000)
  directionLo := (8749154135334173951/2000000000000000000)
  directionHi := (437457706766708697551/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree082.table
  base := (-3737978220764304622584315949823743048887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-62029607710727723139908226987020000000000000)
      constant := (1563876566777791593563173667899459909994357817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree082.table
  base := (-3738047497482822422333482417238483975643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-257653634755202439055830887891180000000000000)
      constant := (6556287151044056889473149482870465781459938117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8749154135334173951/2000000000000000000)
  centralHi := (437457706766708697551/100000000000000000000)
  directionLo := (88029955920420665229/20000000000000000000)
  directionHi := (220074889801051663073/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree083.table
  base := (-7510176677505841843867191071601708838259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-125525473009326099304815144483340000000000000)
      constant := (3203719388990252364214093111363147470934910269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree083.table
  base := (-3755149805484605135739323045017674972151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-260699695074710889988716517019030000000000000)
      constant := (6715510391128371735148645549875947939541472169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88029955920420665229/20000000000000000000)
  centralHi := (220074889801051663073/50000000000000000000)
  directionLo := (221412743399049060859/50000000000000000000)
  directionHi := (442825486798098121719/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree084.table
  base := (-7543064497503478666104723031660651469001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-126991730597196752329813834992640000000000000)
      constant := (3280596617191445685909604385803672148565368391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree084.table
  base := (-7543173560845566505142346932222019857033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-527491510788438681843204292293760000000000000)
      constant := (13753285595685170429192574866271049950624941527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221412743399049060859/50000000000000000000)
  centralHi := (442825486798098121719/100000000000000000000)
  directionLo := (22274256162224868701/5000000000000000000)
  directionHi := (445485123244497374021/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree085.table
  base := (-7574622521817474913020566989723118498157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-128457988185067405354812525501940000000000000)
      constant := (3358384790360443363483993909442677435853052387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree085.table
  base := (-7574719270163651255871634165797691808723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-533583631427455583708975550549460000000000000)
      constant := (14079368636422117887512311453699641024103170637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22274256162224868701/5000000000000000000)
  centralHi := (445485123244497374021/100000000000000000000)
  directionLo := (448128975080118486179/100000000000000000000)
  directionHi := (22406448754005924309/5000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree086.table
  base := (-7604853050302626239331080691121912825841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-129924245772938058379811216011240000000000000)
      constant := (3437083884098085869836375842959927626830652831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree086.table
  base := (-3802469432787856148433462351589056203853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-269837876033236242787373404402580000000000000)
      constant := (7204634905786644505137666725443218435959497107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448128975080118486179/100000000000000000000)
  centralHi := (22406448754005924309/5000000000000000000)
  directionLo := (450757320052098428299/100000000000000000000)
  directionHi := (4507573200520984283/1000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree087.table
  base := (-7633758102055132766684354834450813878843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-131390503360808711404809906520540000000000000)
      constant := (3516693876983781617876185592134041315559354613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree087.table
  base := (-3816917106067629423702653942779932955911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-272883936352744693720259033530430000000000000)
      constant := (7371494519835640730637199159159314748552851609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (450757320052098428299/100000000000000000000)
  centralHi := (4507573200520984283/1000000000000000000)
  directionLo := (90674085571290397543/20000000000000000000)
  directionHi := (113342606964112996929/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree088.table
  base := (-7661339450141114511591720148338802586381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-132856760948679364429808597029840000000000000)
      constant := (3597214750207072140348254449264993643361083971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree088.table
  base := (-1915351736479890607511354820769582673281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19855000000000000000000000000000000000000000
      center := (61275)
      previous := (0)
      next := (38000)
      square := (224322271591707626840414548175000000000000)
      linear := (-25084545152023013150285878423480000000000000)
      constant := (685478465875027451960573740711687974408802298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90674085571290397543/20000000000000000000)
  centralHi := (113342606964112996929/25000000000000000000)
  directionLo := (455968560461063781373/100000000000000000000)
  directionHi := (227984280230531890687/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree089.table
  base := (-7687598651995707001615709210681394428957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-134323018536550017454807287539140000000000000)
      constant := (3678646487245128084440671506233891086503195187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree089.table
  base := (-3843829251276542041289154822140863735699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-278976056991761595586030291786130000000000000)
      constant := (7710940688800872186629127247577309931160931981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455968560461063781373/100000000000000000000)
  centralHi := (227984280230531890687/50000000000000000000)
  directionLo := (57318996551526115999/12500000000000000000)
  directionHi := (458551972412208927993/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree090.table
  base := (-964067134504691629649310175892457722617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-67894638062210335239902989024220000000000000)
      constant := (1880494536790198140431794165059127664083024988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree090.table
  base := (-1542518028430294984783291222978178422609/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-112808846924508018607566368365592000000000000)
      constant := (3153410873936318199025215800521770188322016271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57318996551526115999/12500000000000000000)
  centralHi := (458551972412208927993/100000000000000000000)
  directionLo := (230560455562808763739/50000000000000000000)
  directionHi := (461120911125617527479/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree091.table
  base := (-1547231184994781553704790389051268007599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-27451106742458264700960933711548000000000000)
      constant := (768848499290670964637715291296253097707382209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree091.table
  base := (-7736202971139115172804913975454093889363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-570136355261556994903603100083660000000000000)
      constant := (16116045177160420456401093058310199724818734797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230560455562808763739/50000000000000000000)
  centralHi := (461120911125617527479/100000000000000000000)
  directionLo := (3622465759086132603/781250000000000000)
  directionHi := (92735123432604994637/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree092.table
  base := (-7758456256211702754888474280587340368441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-138721791300161976529803359067040000000000000)
      constant := (3928406744645974211043188179512928906031209431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree092.table
  base := (-1551699592267035153454921472355702388109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-115245695180114779353874871667872000000000000)
      constant := (3293770751517639910267833573016494563985010771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3622465759086132603/781250000000000000)
  centralHi := (92735123432604994637/20000000000000000000)
  directionLo := (1165540811237707529/250000000000000000)
  directionHi := (466216324495083011601/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree093.table
  base := (-1944859749934043625117019380214849036971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-70094024444016314777401024788170000000000000)
      constant := (2006740904146020429087288785204686333133549322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree093.table
  base := (-7779475966652745732199785447669566130543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-582320596539590798635145616595060000000000000)
      constant := (16825480073665150638244771344764675681851751217) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1165540811237707529/250000000000000000)
  centralHi := (466216324495083011601/100000000000000000000)
  directionLo := (468743260751444809911/100000000000000000000)
  directionHi := (58592907593930601239/12500000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree094.table
  base := (-7799104973774221725137577560374141737773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-141654306475903282579800740085640000000000000)
      constant := (4099467678710985596063592707347950730303966243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree094.table
  base := (-7799137737711665804510016268522265331929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-588412717178607700500916874850760000000000000)
      constant := (17185924092603448453888083036002718928036009351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468743260751444809911/100000000000000000000)
  centralHi := (58592907593930601239/12500000000000000000)
  directionLo := (117814161864695149281/25000000000000000000)
  directionHi := (3770053179670244777/800000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree095.table
  base := (-7817454898518581329607265865885986316973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-143120564063773935604799430594940000000000000)
      constant := (4186364348262283678930598108157865571163233443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree095.table
  base := (-7817483934627479715960786250155514401513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22990000000000000000000000000000000000000000
      center := (70950)
      previous := (0)
      next := (44000)
      square := (259741577632503567920480003150000000000000)
      linear := (-31289728306190768545615164900340000000000000)
      constant := (923693988714136101711699554538442472390921613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117814161864695149281/25000000000000000000)
  centralHi := (3770053179670244777/800000000000000000)
  directionLo := (473756700267428261813/100000000000000000000)
  directionHi := (236878350133714130907/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree096.table
  base := (-7834489408154634278761669658966662425513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-144586821651644588629798121104240000000000000)
      constant := (4274171810217862400119133823545462678327732583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree096.table
  base := (-7834515138205611561027945676347619201807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-600596958456641504232459391362160000000000000)
      constant := (17918265127190401344276597229202019645645868433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473756700267428261813/100000000000000000000)
  centralHi := (236878350133714130907/50000000000000000000)
  directionLo := (476243629167335216257/100000000000000000000)
  directionHi := (238121814583667608129/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree097.table
  base := (-1570041812280220368567592284393046158493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-29210615847903048330959362322708000000000000)
      constant := (872578011730054969134650738129100173304547763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree097.table
  base := (-3925115929870427209586870111506941349807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-303344539547829203049115324808930000000000000)
      constant := (9145081047567513416323504880773950294899080433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476243629167335216257/100000000000000000000)
  centralHi := (238121814583667608129/50000000000000000000)
  directionLo := (119679409673475877469/25000000000000000000)
  directionHi := (478717638693903509877/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree098.table
  base := (-983076793843673941696983903162788123191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-73759668413692947339897751061420000000000000)
      constant := (2226259544167339836650455456570443923204266724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree098.table
  base := (-491539659349809520300024910433778248349/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-306390599867337653982000953936780000000000000)
      constant := (9332938334865061847233402691218677058670938648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119679409673475877469/25000000000000000000)
  centralHi := (478717638693903509877/100000000000000000000)
  directionLo := (481178928124309266937/100000000000000000000)
  directionHi := (240589464062154633469/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree099.table
  base := (-7877705710563199387567955823220459353919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-148985594415256547704794192632140000000000000)
      constant := (4543058894662912431749895056425864146714273329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree099.table
  base := (-787772360471899010483774250072211125817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3971000000000000000000000000000000000000000
      center := (12255)
      previous := (0)
      next := (7600)
      square := (44864454318341525368082909635000000000000)
      linear := (-5626121094306292816634301510266000000000000)
      constant := (173140080305788487994644204964982249619380693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481178928124309266937/100000000000000000000)
  centralHi := (240589464062154633469/50000000000000000000)
  directionLo := (483627691664829738661/100000000000000000000)
  directionHi := (241813845832414869331/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree100.table
  base := (-7889483524179756153391728219450762584199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-150451852003127200729792883141440000000000000)
      constant := (4634509473568148440008547285043846859744232809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree100.table
  base := (-3944749687606026697376305381834119186813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-312482720506354555847772212192480000000000000)
      constant := (9714379285780958270918177134854103839800821347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483627691664829738661/100000000000000000000)
  centralHi := (241813845832414869331/50000000000000000000)
  directionLo := (486064118629676330611/100000000000000000000)
  directionHi := (121516029657419082653/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree101.table
  base := (-3949974065068220987156380168563287835803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-75959054795498926877395786825370000000000000)
      constant := (2363435410729422316068481573231157079349965973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree101.table
  base := (-1974990542525704965629577772223341452569/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-315528780825863006780657841320330000000000000)
      constant := (9907962935003538987264269249013829444020667022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486064118629676330611/100000000000000000000)
  centralHi := (121516029657419082653/25000000000000000000)
  directionLo := (244244196805899825239/50000000000000000000)
  directionHi := (488488393611799650479/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree102.table
  base := (-1581819965526211890286842090701728853223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-30676873435773701355958052832008000000000000)
      constant := (964028587032162304068007846903561358596157193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree102.table
  base := (-1977278065596518998934414995325551578221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-318574841145371457713543470448180000000000000)
      constant := (10103455358523766354461218301677829163023456998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244244196805899825239/50000000000000000000)
  centralHi := (488488393611799650479/100000000000000000000)
  directionLo := (490900696646102699563/100000000000000000000)
  directionHi := (122725174161525674891/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree103.table
  base := (-7916938881310563544008850780696097302057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030000000000000000000000000000000000000000
      center := (3150)
      previous := (0)
      next := (2000)
      square := (11636964983100420833322940550000000000000)
      linear := (-1503404123948923881599892763780000000000000)
      constant := (47711901086081646208301581444778301977888129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree103.table
  base := (-7916949893445347015374182679412419774259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-643241802929759817292858199152060000000000000)
      constant := (20601713102139406979841140839748516091840592621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490900696646102699563/100000000000000000000)
  centralHi := (122725174161525674891/25000000000000000000)
  directionLo := (493301203365470604517/100000000000000000000)
  directionHi := (246650601682735302259/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree104.table
  base := (-7923465525471250770698105664250351910549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-156316882354609812829787645178640000000000000)
      constant := (5009419449089989339715555058463328016580985659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree104.table
  base := (-3169390110770256734414098363412452893/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8736200000000000000000000000000000000000000
      center := (26961)
      previous := (0)
      next := (16720)
      square := (98701799500351355809782401197000000000000)
      linear := (-12986678471375534383172589148155200000000000)
      constant := (420006660319009463057713736425561832259043350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493301203365470604517/100000000000000000000)
  centralHi := (246650601682735302259/50000000000000000000)
  directionLo := (495690085149999573321/100000000000000000000)
  directionHi := (247845042574999786661/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree105.table
  base := (-396433998387154697499900833754471649023/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-15778313994248046585478633568794000000000000)
      constant := (510542384462880447949009123844542620551029986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree105.table
  base := (-7928688602126542925874354658065423869209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-655426044207793621024400715663460000000000000)
      constant := (21402770450211936166264661296502094219969081671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495690085149999573321/100000000000000000000)
  centralHi := (247845042574999786661/50000000000000000000)
  directionLo := (124516877317445974251/25000000000000000000)
  directionHi := (99613501853956779401/20000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree106.table
  base := (-7932582392321884490833639736529839039851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-159249397530351118879785026197240000000000000)
      constant := (5202338996528721827721385510467994937626220741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree106.table
  base := (-3966295018487665929931383690003420278913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-330759082423405261445085986959580000000000000)
      constant := (10904512698794282216750872362489540598796801247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124516877317445974251/25000000000000000000)
  centralHi := (99613501853956779401/20000000000000000000)
  directionLo := (500433639021597656647/100000000000000000000)
  directionHi := (62554204877699707081/12500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree107.table
  base := (-495948310175309278396126370426349375479/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-80357827559110885952391858353270000000000000)
      constant := (2650082451527068676113438689038939875804346312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree107.table
  base := (-396758986531618907668576641561194658917/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43681000000000000000000000000000000000000000
      center := (134805)
      previous := (0)
      next := (83600)
      square := (493508997501756779048912005985000000000000)
      linear := (-66761028548582742475594323217486000000000000)
      constant := (2221909785156488385379601432596027912207693046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree107.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500433639021597656647/100000000000000000000)
  centralHi := (62554204877699707081/12500000000000000000)
  directionLo := (20111545354391487913/4000000000000000000)
  directionHi := (251394316929893598913/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree108.table
  base := (-992056478084911589165080666355567886527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-81090956353046212464891203607920000000000000)
      constant := (2699450781330789698546465522918295121167340228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree108.table
  base := (-3968228907887247384627292745509462301337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-336851203062422163310857245215280000000000000)
      constant := (11316493903172719280058523693727641177215298503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree108.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20111545354391487913/4000000000000000000)
  centralHi := (251394316929893598913/50000000000000000000)
  directionLo := (505132649521671277723/100000000000000000000)
  directionHi := (126283162380417819431/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree109.table
  base := (-1587283821500997851556914363819834276481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-32729634058792615590956219545028000000000000)
      constant := (1099709794795309031715520806071997378160813071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree109.table
  base := (-317456976423850372391212376994130937189/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 17472400000000000000000000000000000000000000
      center := (53922)
      previous := (0)
      next := (33440)
      square := (197403599000702711619564802394000000000000)
      linear := (-27191781070554449139499429947450400000000000)
      constant := (922027810270694848328806345004026966532647291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree109.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505132649521671277723/100000000000000000000)
  centralHi := (126283162380417819431/25000000000000000000)
  directionLo := (507465838147727960701/100000000000000000000)
  directionHi := (253732919073863980351/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree110.table
  base := (-7935074926831310631071930529948539248883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-165114427881833730979779788234440000000000000)
      constant := (5599107135773172404268579683619175947108600253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree110.table
  base := (-7935079620564311456454824348851437145701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39710000000000000000000000000000000000000000
      center := (122550)
      previous := (0)
      next := (76000)
      square := (448644543183415253680829096350000000000000)
      linear := (-62353331582079830032114273358360000000000000)
      constant := (2133838199838526682743407202143310943094421329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree110.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507465838147727960701/100000000000000000000)
  centralHi := (253732919073863980351/50000000000000000000)
  directionLo := (509788348396830732643/100000000000000000000)
  directionHi := (127447087099207683161/25000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree111.table
  base := (-1983104846469623260268869882545332616843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-83290342734852192002389239371870000000000000)
      constant := (2850288023478198824118161867641798132535825226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree111.table
  base := (-1983105884988818536605465363840075096477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-345989384020947516109514132598830000000000000)
      constant := (11948781313298304149735816930334808359421576326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree111.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509788348396830732643/100000000000000000000)
  centralHi := (127447087099207683161/25000000000000000000)
  directionLo := (64012540694597603599/12500000000000000000)
  directionHi := (512100325556780828793/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree112.table
  base := (-792845257701394330442042522783134920311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-16804694305757503702977716925304000000000000)
      constant := (580295570654629507156325937057041721630420601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree112.table
  base := (-1585691250640825859394407769473942377347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-139614177736182386816959904690672000000000000)
      constant := (4865344507639522226194690209404712723015105693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree112.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64012540694597603599/12500000000000000000)
  centralHi := (512100325556780828793/100000000000000000000)
  directionLo := (257200955825184168733/50000000000000000000)
  directionHi := (514401911650368337467/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree113.table
  base := (-7923174583048149346419755598802965352579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-169513200645445690054775859762340000000000000)
      constant := (5906246113664328207849741100043269340574489389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree113.table
  base := (-7923177836086539711373826869735386909889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-704163009319928835950570781709060000000000000)
      constant := (24759699929716845277773360729504618564389138591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree113.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257200955825184168733/50000000000000000000)
  centralHi := (514401911650368337467/100000000000000000000)
  directionLo := (516693245537181174177/100000000000000000000)
  directionHi := (258346622768590587089/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree114.table
  base := (-395829273918621925684256996266499290847/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-17097945823331634307977455027164000000000000)
      constant := (601044726752127946527556572428693418046808354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree114.table
  base := (-3958294178377843497318678010268085703911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11495000000000000000000000000000000000000000
      center := (35475)
      previous := (0)
      next := (22000)
      square := (129870788816251783960240001575000000000000)
      linear := (-18690924472603835205693211578020000000000000)
      constant := (663065652583613463531129352574373670966708611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree114.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516693245537181174177/100000000000000000000)
  centralHi := (258346622768590587089/50000000000000000000)
  directionLo := (259487231505684222373/50000000000000000000)
  directionHi := (518974463011368444747/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree115.table
  base := (-790868532995799842666394534310888616511/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (32445)
      previous := (0)
      next := (20600)
      square := (119860739325934334583226287665000000000000)
      linear := (-17244571582118699610477324078094000000000000)
      constant := (611555916740665151437540712535880782667434801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree115.table
  base := (-1977171969162909598129829583389138220001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-358173625298981319841056649110230000000000000)
      constant := (12818553570447623281420108493630283106824272638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree115.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259487231505684222373/50000000000000000000)
  centralHi := (518974463011368444747/100000000000000000000)
  directionLo := (260622848447776482869/50000000000000000000)
  directionHi := (521245696895552965739/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree116.table
  base := (-7899474198233183405196197524620535211021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-173911973409057649129771931290240000000000000)
      constant := (6221581812679359944170082470899540741946278211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree116.table
  base := (-7899476451299017613643626380823147942173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-722439371236979541547884556476160000000000000)
      constant := (26081536955445279035528864372749024074737941187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree116.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260622848447776482869/50000000000000000000)
  centralHi := (521245696895552965739/100000000000000000000)
  directionLo := (261753538565538362481/50000000000000000000)
  directionHi := (523507077131076724963/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree117.table
  base := (-1577790427570806717593407572693810676753/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-35075646199385660430954124359908000000000000)
      constant := (1265703040551911764965656219172877362530327423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree117.table
  base := (-7888954131006795877931336073130719802169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-728531491875996443413655814731860000000000000)
      constant := (26529784239629862860391485911052147028321455911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree117.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261753538565538362481/50000000000000000000)
  centralHi := (523507077131076724963/100000000000000000000)
  directionLo := (262879365432376394023/50000000000000000000)
  directionHi := (525758730864752788047/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree118.table
  base := (-1575423839676219392128984587561961446711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (64890)
      previous := (0)
      next := (41200)
      square := (239721478651868669166452575330000000000000)
      linear := (-35368897716959791035953862461768000000000000)
      constant := (1287271867424292060554009268883139151011843001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree118.table
  base := (-1575424192296460937727646602677759983629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-146924722503002669055885414597512000000000000)
      constant := (5396369798290491218006873126249848766155101651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree118.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262879365432376394023/50000000000000000000)
  centralHi := (525758730864752788047/100000000000000000000)
  directionLo := (264000391266143768859/50000000000000000000)
  directionHi := (528000782532287537719/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree119.table
  base := (-1965993856218508609839409751851384351377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-89155373086334804102384001409070000000000000)
      constant := (3272557107643513217668089266061822326832482814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree119.table
  base := (-1965994246092517649251396682276168665953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-370357866577015123572599165621630000000000000)
      constant := (13718865604546992080086366819554634353005014014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree119.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264000391266143768859/50000000000000000000)
  centralHi := (528000782532287537719/100000000000000000000)
  directionLo := (530233353938528123277/100000000000000000000)
  directionHi := (265116676969264061639/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree120.table
  base := (-1962380214603519195439008333401326911233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-89888501880270130614883346663720000000000000)
      constant := (3327389918410213222709379910196290645597458206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree120.table
  base := (-1569904447544951562962412931470549519479/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-149361570758609429802193917899792000000000000)
      constant := (5579486178178436256674377192462674926439637801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree120.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530233353938528123277/100000000000000000000)
  centralHi := (265116676969264061639/50000000000000000000)
  directionLo := (16639267635458798599/3125000000000000000)
  directionHi := (532456564334681555169/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree121.table
  base := (-7833755536563164788534710885787145650591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-181243261348410914254765383836740000000000000)
      constant := (6765356201323165703063221145102374171792880081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree121.table
  base := (-3916878378213176794178992422150842758127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19855000000000000000000000000000000000000000
      center := (61275)
      previous := (0)
      next := (38000)
      square := (224322271591707626840414548175000000000000)
      linear := (-34222726110548365948942765807030000000000000)
      constant := (1289134001605611578942099018558494003407477683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree121.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16639267635458798599/3125000000000000000)
  centralHi := (532456564334681555169/100000000000000000000)
  directionLo := (534670530492643963673/100000000000000000000)
  directionHi := (267335265246321981837/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree122.table
  base := (-7816679493767519457261534909242997766751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-182709518936281567279764074346040000000000000)
      constant := (6876843308429804249706365045083721036692538641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree122.table
  base := (-3908340286272361684331228743238866317301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-379496047535540476371256053005180000000000000)
      constant := (14414141320493480363734822612267643080393975019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree122.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (534670530492643963673/100000000000000000000)
  centralHi := (267335265246321981837/50000000000000000000)
  directionLo := (536875366776571114463/100000000000000000000)
  directionHi := (16777355211767847327/3125000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree123.table
  base := (-7798292761712437586515278276202715642133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-184175776524152220304762764855340000000000000)
      constant := (6989241157804192771612069318935135389752611003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree123.table
  base := (-7798293715659780149892775090866986723263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-765084215710097854608283364266060000000000000)
      constant := (29299434706590619076104064907060969152941148897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree123.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (536875366776571114463/100000000000000000000)
  centralHi := (16777355211767847327/3125000000000000000)
  directionLo := (134767796302953575791/25000000000000000000)
  directionHi := (107814237042362860633/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree124.table
  base := (-1944648842408568569613827533502554789419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-92821017056011436664880727682320000000000000)
      constant := (3551274874568081388750762609686222792478107658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree124.table
  base := (-1555719242628547858401447432929218075491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 87362000000000000000000000000000000000000000
      center := (269610)
      previous := (0)
      next := (167200)
      square := (987017995003513558097824011970000000000000)
      linear := (-154235267269822951294810924504352000000000000)
      constant := (5954880846187765544898219795018186825244477629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree124.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134767796302953575791/25000000000000000000)
  centralHi := (107814237042362860633/20000000000000000000)
  directionLo := (270629047775669602319/50000000000000000000)
  directionHi := (541258095551339204639/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree125.table
  base := (-7757587344594842382445363382388440639139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-187108291699893526354760145873940000000000000)
      constant := (7216769082138615494855832904062491033259374349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree125.table
  base := (-7757588090403253040164636000101887809539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-777268456988131658339825880777460000000000000)
      constant := (30253191212921667652909966222505799438591526941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree125.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270629047775669602319/50000000000000000000)
  centralHi := (541258095551339204639/100000000000000000000)
  directionLo := (6792952566746738769/1250000000000000000)
  directionHi := (543436205339739101521/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree126.table
  base := (-7735268711722817488006716539766155901007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-188574549287764179379758836383240000000000000)
      constant := (7331899156544960804345761129203260852046216737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree126.table
  base := (-1933817342776656464257925829474214216271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-391680288813574280102798569516580000000000000)
      constant := (15367897825752707348563460570507653697638132898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree126.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6792952566746738769/1250000000000000000)
  centralHi := (543436205339739101521/100000000000000000000)
  directionLo := (545605619974948133603/100000000000000000000)
  directionHi := (136401404993737033401/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree127.table
  base := (-7711639494426174510862811103886391586221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (324450)
      previous := (0)
      next := (206000)
      square := (1198607393259343345832262876650000000000000)
      linear := (-190040806875634832404757526892540000000000000)
      constant := (7447939972106863500090399903945199271661781411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree127.table
  base := (-3855820038682396071270019949583187302779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-394726349133082731035684198644430000000000000)
      constant := (15611108772862098725309275738449341795427310501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree127.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545605619974948133603/100000000000000000000)
  centralHi := (136401404993737033401/25000000000000000000)
  directionLo := (13694161069193869261/2500000000000000000)
  directionHi := (547766442767754770441/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree128.table
  base := (-1921674928644797123839446512397473798269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-95753532231752742714878108700920000000000000)
      constant := (3782445764296129699072151128952110400948328358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree128.table
  base := (-7506543193265901154508954409223464351/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 218405000000000000000000000000000000000000000
      center := (674025)
      previous := (0)
      next := (418000)
      square := (2467544987508783895244560029925000000000000)
      linear := (-397772409452591181968569827772280000000000000)
      constant := (15856228447336330158887064736522603445086192128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree128.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13694161069193869261/2500000000000000000)
  centralHi := (547766442767754770441/100000000000000000000)
  directionLo := (274959387499605295393/50000000000000000000)
  directionHi := (549918774999210590787/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree129.table
  base := (-3830224696343549729238249323023140920877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-96486661025688069227377453955570000000000000)
      constant := (3841376912891804203583637920155852497970415907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree129.table
  base := (-7660449848214008234904212711734657784547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-801636939544199265802910913800260000000000000)
      constant := (32206513697499508200841016116667608413313202493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree129.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274959387499605295393/50000000000000000000)
  centralHi := (549918774999210590787/100000000000000000000)
  directionLo := (27603135798801231659/5000000000000000000)
  directionHi := (552062715976024633181/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 63
  qDenominator := 103
  table := BinomialMassData.Q63_103.Degree130.table
  base := (-3816444274015580728777614405966399265957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (162225)
      previous := (0)
      next := (103000)
      square := (599303696629671672916131438325000000000000)
      linear := (-97219789819623395739876799210220000000000000)
      constant := (3900763431738177851432520028755202470187462187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q63_103.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 129
  qDenominator := 209
  table := BinomialMassData.Q129_209.Degree130.table
  base := (-7632888950675336536703506455618673618903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (1348050)
      previous := (0)
      next := (836000)
      square := (4935089975017567790489120059850000000000000)
      linear := (-807729060183216167668682172055960000000000000)
      constant := (32704387953401824562634225252945920717652698057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q129_209.Degree130.checked
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
end ForestUnimodality.Stage170KernelData.Cell303.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell303
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 130 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 130 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 130 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel130.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell303

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell303.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 130 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell303.Kernel349

