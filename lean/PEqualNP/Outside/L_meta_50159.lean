import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50159

open PEqualNP.CircuitLowerBounds

def xsOfN (t : Nat) : List Bool :=
  (List.ofFn (fun i : Fin 5 => decide (i.val < t))) ++ [false, true]

def xsOf (t : Fin 6) : List Bool := xsOfN t.val

def gateMask (vs : List Nat) (g : Gate) : Nat :=
  match g.op, g.inputs with
  | .and, [] => 63
  | .and, [a] => vs.getD a 0
  | .and, a :: b :: _ => (vs.getD a 0) &&& (vs.getD b 0)
  | .or, [] => 0
  | .or, [a] => vs.getD a 0
  | .or, a :: b :: _ => (vs.getD a 0) ||| (vs.getD b 0)
  | .not, [] => 63
  | .not, a :: _ => 63 ^^^ (vs.getD a 0)
  | _, _ => 0

def foldMasks (gs : List Gate) (vs : List Nat) : List Nat :=
  gs.foldl (fun acc g => acc ++ [gateMask acc g]) vs

def setMask (vs : List Nat) : Nat :=
  vs.foldl (fun m v => m ||| (1 <<< v)) 0

def bT0 (h : Nat) : List Nat :=
  if h < 125 then
    if h < 62 then
      if h < 31 then
        []
      else
        if h < 46 then
          if h < 38 then
            if h < 34 then
              []
            else
              if h < 36 then
                []
              else
                if h < 37 then
                  [60241274532794466308]
                else
                  []
          else
            []
        else
          []
    else
      []
  else
    []

def bT1 (h : Nat) : List Nat :=
  if h < 125 then
    if h < 62 then
      if h < 31 then
        []
      else
        if h < 46 then
          if h < 38 then
            if h < 34 then
              if h < 32 then
                []
              else
                if h < 33 then
                  [60241274541384400901]
                else
                  []
            else
              if h < 36 then
                []
              else
                if h < 37 then
                  [60241274532794466308]
                else
                  [60241274532794466309]
          else
            if h < 42 then
              []
            else
              if h < 44 then
                []
              else
                if h < 45 then
                  []
                else
                  [60241274532794466317]
        else
          if h < 54 then
            if h < 50 then
              if h < 48 then
                if h < 47 then
                  []
                else
                  [60241274532794466821]
              else
                []
            else
              []
          else
            []
    else
      if h < 93 then
        if h < 77 then
          if h < 69 then
            []
          else
            if h < 73 then
              if h < 71 then
                if h < 70 then
                  [60241274532794466341]
                else
                  []
              else
                []
            else
              []
        else
          if h < 85 then
            []
          else
            if h < 89 then
              if h < 87 then
                []
              else
                if h < 88 then
                  [60241274532794597381]
                else
                  []
            else
              []
      else
        []
  else
    []

def bT2 (h : Nat) : List Nat :=
  if h < 125 then
    if h < 62 then
      if h < 31 then
        if h < 15 then
          if h < 7 then
            if h < 3 then
              if h < 1 then
                [60241274542458142725]
              else
                []
            else
              []
          else
            []
        else
          if h < 23 then
            if h < 19 then
              []
            else
              if h < 21 then
                []
              else
                if h < 22 then
                  []
                else
                  [60241276731817722373]
          else
            if h < 27 then
              if h < 25 then
                []
              else
                if h < 26 then
                  [60241274567154204685]
                else
                  []
            else
              if h < 29 then
                []
              else
                if h < 30 then
                  []
                else
                  [60241274541451509765]
      else
        if h < 46 then
          if h < 38 then
            if h < 34 then
              if h < 32 then
                []
              else
                if h < 33 then
                  [60241274541384400901]
                else
                  [60241274541384400902]
            else
              if h < 36 then
                []
              else
                if h < 37 then
                  [60241274532794466308]
                else
                  [60241274532794466309]
          else
            if h < 42 then
              if h < 40 then
                if h < 39 then
                  [60241274532794466310]
                else
                  []
              else
                if h < 41 then
                  []
                else
                  [60241274541384400910]
            else
              if h < 44 then
                if h < 43 then
                  []
                else
                  [60241274541384401414]
              else
                if h < 45 then
                  []
                else
                  [60241274532794466317]
        else
          if h < 54 then
            if h < 50 then
              if h < 48 then
                if h < 47 then
                  [60241274532794466318]
                else
                  [60241274532794466821, 60243526332608151565]
              else
                if h < 49 then
                  [60241274532794466822]
                else
                  []
            else
              if h < 52 then
                []
              else
                if h < 53 then
                  [60241274532794467077]
                else
                  []
          else
            if h < 58 then
              if h < 56 then
                if h < 55 then
                  []
                else
                  [60817735285097889805]
              else
                if h < 57 then
                  [60241274532794466830]
                else
                  []
            else
              []
    else
      if h < 93 then
        if h < 77 then
          if h < 69 then
            if h < 65 then
              []
            else
              if h < 67 then
                if h < 66 then
                  [60241274541384400934]
                else
                  []
              else
                []
          else
            if h < 73 then
              if h < 71 then
                if h < 70 then
                  [60241274532794466341]
                else
                  [60241274532794466342]
              else
                []
            else
              []
        else
          if h < 85 then
            if h < 81 then
              if h < 79 then
                if h < 78 then
                  [60250281732049207333]
                else
                  [60241274532794466350]
              else
                if h < 80 then
                  []
                else
                  [60241274532794466854]
            else
              if h < 83 then
                []
              else
                if h < 84 then
                  [60241274541384531974]
                else
                  []
          else
            if h < 89 then
              if h < 87 then
                if h < 86 then
                  [60241274532794466357]
                else
                  []
              else
                if h < 88 then
                  [60241274532794597381]
                else
                  [60241274532794597382]
            else
              []
      else
        if h < 109 then
          if h < 101 then
            if h < 97 then
              if h < 95 then
                []
              else
                if h < 96 then
                  []
                else
                  [60241274532794597390]
            else
              if h < 99 then
                if h < 98 then
                  []
                else
                  [60241274532794597894]
              else
                []
          else
            if h < 105 then
              []
            else
              if h < 107 then
                []
              else
                if h < 108 then
                  [60241274532794598405]
                else
                  []
        else
          if h < 117 then
            if h < 113 then
              if h < 111 then
                if h < 110 then
                  [62547117542008160293]
                else
                  []
              else
                if h < 112 then
                  [60241274532794466885]
                else
                  [60241274532794662917]
            else
              []
          else
            if h < 121 then
              if h < 119 then
                []
              else
                if h < 120 then
                  []
                else
                  [60241274532794597414]
            else
              []
  else
    if h < 188 then
      if h < 156 then
        if h < 140 then
          if h < 132 then
            []
          else
            if h < 136 then
              if h < 134 then
                if h < 133 then
                  [60241274541384663045]
                else
                  []
              else
                []
            else
              []
        else
          if h < 148 then
            []
          else
            if h < 152 then
              []
            else
              if h < 154 then
                []
              else
                if h < 155 then
                  []
                else
                  [60241274545679368197]
      else
        if h < 172 then
          if h < 164 then
            if h < 160 then
              if h < 158 then
                if h < 157 then
                  [60241274532794613765]
                else
                  []
              else
                []
            else
              []
          else
            []
        else
          if h < 180 then
            if h < 176 then
              if h < 174 then
                []
              else
                if h < 175 then
                  []
                else
                  [60385389720870322693]
            else
              []
          else
            []
    else
      if h < 219 then
        if h < 203 then
          []
        else
          if h < 211 then
            if h < 207 then
              if h < 205 then
                []
              else
                if h < 206 then
                  [69464646569649242125]
                else
                  []
            else
              []
          else
            if h < 215 then
              if h < 213 then
                []
              else
                if h < 214 then
                  [60241837482748018693]
                else
                  []
            else
              []
      else
        if h < 235 then
          []
        else
          if h < 243 then
            if h < 239 then
              []
            else
              if h < 241 then
                if h < 240 then
                  []
                else
                  [60241274670233419813]
              else
                []
          else
            []

def bT3 (h : Nat) : List Nat :=
  if h < 125 then
    if h < 62 then
      if h < 31 then
        if h < 15 then
          if h < 7 then
            if h < 3 then
              if h < 1 then
                [60241274542458142725, 60241274670233420326]
              else
                if h < 2 then
                  [60241274542458142726]
                else
                  []
            else
              if h < 5 then
                if h < 4 then
                  []
                else
                  [60241274545679630341]
              else
                if h < 6 then
                  [60241274670233419829, 69464646569649373198]
                else
                  [60241276740474765318]
          else
            if h < 11 then
              if h < 9 then
                if h < 8 then
                  []
                else
                  [60241837491338084358]
              else
                if h < 10 then
                  [60241274542458142734]
                else
                  []
            else
              if h < 13 then
                if h < 12 then
                  [60241274542458143238]
                else
                  []
              else
                []
        else
          if h < 23 then
            if h < 19 then
              if h < 17 then
                []
              else
                if h < 18 then
                  []
                else
                  [60241276740407656966]
            else
              if h < 21 then
                []
              else
                if h < 22 then
                  [60241274575744139278, 60241276731884831238]
                else
                  [60241276731817722373]
          else
            if h < 27 then
              if h < 25 then
                if h < 24 then
                  [60241276731817722374]
                else
                  []
              else
                if h < 26 then
                  [60241274567154204685, 60242118957724729349]
                else
                  [60241274567154204686]
            else
              if h < 29 then
                if h < 28 then
                  [60241276731817722629, 60243526366967889933]
                else
                  []
              else
                if h < 30 then
                  [62547117679447113765]
                else
                  [60241274541451509765]
      else
        if h < 46 then
          if h < 38 then
            if h < 34 then
              if h < 32 then
                [60241274541451509766, 60241276731817722382, 60241837482748035077]
              else
                if h < 33 then
                  [60241274541384400901]
                else
                  [60241274541384400902, 60241274542458142758]
            else
              if h < 36 then
                if h < 35 then
                  []
                else
                  [60817735319457628173]
              else
                if h < 37 then
                  [60241274532794466308, 60241274567154205198]
                else
                  [60241274532794466309]
          else
            if h < 42 then
              if h < 40 then
                if h < 39 then
                  [60241274532794466310]
                else
                  [60241274541451509774]
              else
                if h < 41 then
                  [60241274670233550886]
                else
                  [60241274541384400910, 60241274541451510278]
            else
              if h < 44 then
                if h < 43 then
                  []
                else
                  [60241274541384401414, 60243526341198086158]
              else
                if h < 45 then
                  []
                else
                  [60241274532794466317, 60241274601513943093]
        else
          if h < 54 then
            if h < 50 then
              if h < 48 then
                if h < 47 then
                  [60241274532794466318]
                else
                  [60241274532794466821, 60243526332608151565]
              else
                if h < 49 then
                  [60241274532794466822, 60241274541384401670, 60243526332608151566]
                else
                  []
            else
              if h < 52 then
                if h < 51 then
                  []
                else
                  [60241274542458273798, 60817735293687824398]
              else
                if h < 53 then
                  [60241274532794467077]
                else
                  [60241274532794467078]
          else
            if h < 58 then
              if h < 56 then
                if h < 55 then
                  []
                else
                  [60241276731817722406, 60817735285097889805]
              else
                if h < 57 then
                  [60241274532794466830, 60817735285097889806]
                else
                  [60241278930841109509, 60819987084911575053]
            else
              if h < 60 then
                if h < 59 then
                  [60241274567154204718, 60243526332608152078]
                else
                  []
              else
                if h < 61 then
                  []
                else
                  [60241274532794467086, 60817735285097890062]
    else
      if h < 93 then
        if h < 77 then
          if h < 69 then
            if h < 65 then
              if h < 63 then
                []
              else
                if h < 64 then
                  [60241274541451509798, 60241837482748280838, 60817735285097890566]
                else
                  []
            else
              if h < 67 then
                if h < 66 then
                  [60241274541384400934]
                else
                  [60817735285097890318]
              else
                []
          else
            if h < 73 then
              if h < 71 then
                if h < 70 then
                  [60241274532794466341]
                else
                  [60241274532794466342]
              else
                []
            else
              if h < 75 then
                if h < 74 then
                  [60241276731817853446, 60243526332608217102, 60250281740639141926]
                else
                  []
              else
                if h < 76 then
                  []
                else
                  [60241274567154335758]
        else
          if h < 85 then
            if h < 81 then
              if h < 79 then
                if h < 78 then
                  [60250281732049207333]
                else
                  [60241274532794466350, 60250281732049207334]
              else
                if h < 80 then
                  []
                else
                  [60241274532794466854, 60243526332608151598]
            else
              if h < 83 then
                if h < 82 then
                  [60241274541384400950, 60241274541451640838, 60254785331676577829]
                else
                  []
              else
                if h < 84 then
                  [60241274541384531974]
                else
                  []
          else
            if h < 89 then
              if h < 87 then
                if h < 86 then
                  [60241274532794466357, 60241274532794467110]
                else
                  [60241274532794466358, 60241276731817722437, 60250281732049207342]
              else
                if h < 88 then
                  [60241274532794597381]
                else
                  [60241274532794597382, 60250281732049207846, 60817735285097889838]
            else
              if h < 91 then
                if h < 90 then
                  [60245778132421836853]
                else
                  []
              else
                []
      else
        if h < 109 then
          if h < 101 then
            if h < 97 then
              if h < 95 then
                if h < 94 then
                  [60250281732049207349]
                else
                  [60241274532794466366]
              else
                if h < 96 then
                  []
                else
                  [60241274532794466870, 60241274532794597390]
            else
              if h < 99 then
                if h < 98 then
                  []
                else
                  [60241274532794597894, 60243526332608282638]
              else
                if h < 100 then
                  []
                else
                  [60241274542458404869]
          else
            if h < 105 then
              if h < 103 then
                []
              else
                if h < 104 then
                  [60241274532794598150, 60241274541384532998]
                else
                  []
            else
              if h < 107 then
                if h < 106 then
                  [61394196037401313333, 62547117550598094886]
                else
                  [60817735285098020878]
              else
                if h < 108 then
                  [60241274532794598405, 60241274541384401478]
                else
                  [60241274532794598406, 60241274541384597510]
        else
          if h < 117 then
            if h < 113 then
              if h < 111 then
                if h < 110 then
                  [60241344901538791429, 62547117542008160293]
                else
                  [62547117542008160294]
              else
                if h < 112 then
                  [60241274532794466885]
                else
                  [60241274532794466886, 60241274532794662917]
            else
              if h < 115 then
                if h < 114 then
                  [60241274532794662918, 60241277006695629317]
                else
                  []
              else
                if h < 116 then
                  [60243526332608348166]
                else
                  [60241274532794467141, 60241274532794598414, 60313332126832395013]
          else
            if h < 121 then
              if h < 119 then
                if h < 118 then
                  [62556124741262901285]
                else
                  [60241274532794598918, 62547117542008160302]
              else
                if h < 120 then
                  []
                else
                  [60241274532794466894, 60241274532794597414, 62547117542008160806]
            else
              if h < 123 then
                if h < 122 then
                  [60241274532794662926]
                else
                  []
              else
                if h < 124 then
                  [60241274532794663430, 60241274546753110021]
                else
                  []
  else
    if h < 188 then
      if h < 156 then
        if h < 140 then
          if h < 132 then
            if h < 128 then
              if h < 126 then
                [62547117542008160309]
              else
                if h < 127 then
                  []
                else
                  [60259288931303948869]
            else
              if h < 130 then
                if h < 129 then
                  [60250281732049338406]
                else
                  [63700039046615007269]
              else
                if h < 131 then
                  [60241274541451771909]
                else
                  []
          else
            if h < 136 then
              if h < 134 then
                if h < 133 then
                  [60241274532794663941, 60241274541384663045]
                else
                  [60241274541384663046]
              else
                if h < 135 then
                  []
                else
                  [60241277831329350149]
            else
              if h < 138 then
                if h < 137 then
                  [60241274532794597430, 60241274580039106566]
                else
                  []
              else
                []
        else
          if h < 148 then
            if h < 144 then
              if h < 142 then
                if h < 141 then
                  [60241274532794598438]
                else
                  [60241274541384663054]
              else
                if h < 143 then
                  []
                else
                  [60241274541384663558]
            else
              if h < 146 then
                if h < 145 then
                  [60241274532794466918]
                else
                  [60241274532794662950]
              else
                if h < 147 then
                  []
                else
                  [60250281732049223718]
          else
            if h < 152 then
              if h < 150 then
                if h < 149 then
                  []
                else
                  [60241274571449171982]
              else
                if h < 151 then
                  [60385391919893578245]
                else
                  []
            else
              if h < 154 then
                if h < 153 then
                  [60241274541384548358, 62547117542008160838]
                else
                  [60241274545746477061]
              else
                if h < 155 then
                  []
                else
                  [60241274545679368197]
      else
        if h < 172 then
          if h < 164 then
            if h < 160 then
              if h < 158 then
                if h < 157 then
                  [60241274532794613765, 60241274545679368198]
                else
                  [60241274532794613766]
              else
                []
            else
              if h < 162 then
                if h < 161 then
                  [62547117542008291366]
                else
                  []
              else
                if h < 163 then
                  [60241274532794597958]
                else
                  [60241841880794529797]
          else
            if h < 168 then
              if h < 166 then
                if h < 165 then
                  [60241274545679368206]
                else
                  [60241274532794613774, 60241274541384663078, 60241275632306094853, 60250281732049354758]
              else
                if h < 167 then
                  [60241274545679368710, 60241907851492196357]
                else
                  [60241274532794614278]
            else
              if h < 170 then
                []
              else
                if h < 171 then
                  []
                else
                  [60385389729460257286]
        else
          if h < 180 then
            if h < 176 then
              if h < 174 then
                if h < 173 then
                  [60241274679897096198]
                else
                  []
              else
                if h < 175 then
                  [62547117542008160358]
                else
                  [60241556007771373573, 60385389720870322693]
            else
              if h < 178 then
                if h < 177 then
                  [60241274532794614789, 60385389720870322694]
                else
                  []
              else
                []
          else
            if h < 184 then
              if h < 182 then
                if h < 181 then
                  [60385389720870322949]
                else
                  [60241274532794679301]
              else
                if h < 183 then
                  []
                else
                  [60241274541384794118]
            else
              if h < 186 then
                if h < 185 then
                  [60385389720870322702]
                else
                  [69464646604008980493]
              else
                []
    else
      if h < 219 then
        if h < 203 then
          if h < 195 then
            if h < 191 then
              if h < 189 then
                [60241274545679368230]
              else
                if h < 190 then
                  [60241274532794613798]
                else
                  []
            else
              if h < 193 then
                if h < 192 then
                  [60403404119379804677]
                else
                  []
              else
                []
          else
            if h < 199 then
              if h < 197 then
                if h < 196 then
                  []
                else
                  [60385389720870323718]
              else
                []
            else
              if h < 201 then
                if h < 200 then
                  []
                else
                  [60241274738952896549]
              else
                if h < 202 then
                  [69464646578239176718]
                else
                  [60241274807672373829]
        else
          if h < 211 then
            if h < 207 then
              if h < 205 then
                []
              else
                if h < 206 then
                  [69464646569649242125]
                else
                  [60241274545679499270, 69464646569649242126]
            else
              if h < 209 then
                if h < 208 then
                  [69466898369462927373]
                else
                  [60385389720870322726]
              else
                if h < 210 then
                  [60241274671307161638, 60241837491337953286]
                else
                  []
          else
            if h < 215 then
              if h < 213 then
                []
              else
                if h < 214 then
                  [60241837482748018693]
                else
                  [60241837482748018694]
            else
              if h < 217 then
                if h < 216 then
                  [70041107321952665613]
                else
                  [69464646569649242638]
              else
                []
      else
        if h < 235 then
          if h < 227 then
            if h < 223 then
              if h < 221 then
                []
              else
                if h < 222 then
                  []
                else
                  [60241837482748018702, 69464646569649242142]
            else
              if h < 225 then
                if h < 224 then
                  []
                else
                  [60241837482748019206]
              else
                if h < 226 then
                  []
                else
                  [60385389720870453766]
          else
            if h < 231 then
              []
            else
              if h < 233 then
                []
              else
                if h < 234 then
                  [60241837482748019717]
                else
                  []
        else
          if h < 243 then
            if h < 239 then
              if h < 237 then
                if h < 236 then
                  []
                else
                  [60241274678823354406, 60385389720870454278]
              else
                if h < 238 then
                  []
                else
                  [60241837482748084229, 69464646569649242158]
            else
              if h < 241 then
                if h < 240 then
                  [60385389720870322757, 60457447314908250629]
                else
                  [60241274670233419813]
              else
                if h < 242 then
                  [60241274670233419814]
                else
                  []
          else
            if h < 247 then
              if h < 245 then
                []
              else
                if h < 246 then
                  []
                else
                  [60241837482748018726, 69464646569649242166]
            else
              if h < 249 then
                if h < 248 then
                  []
                else
                  [60250281869488160805]
              else
                if h < 250 then
                  [60241274542525251589, 60241274670233419822]
                else
                  []

def bT4 (h : Nat) : List Nat :=
  if h < 125 then
    if h < 62 then
      if h < 31 then
        if h < 15 then
          if h < 7 then
            if h < 3 then
              if h < 1 then
                [60241274542458142725, 60241274670233420326, 60241274738953027622, 60243526470047105070, 60385389720870519302]
              else
                if h < 2 then
                  [60241274541384810502, 60241274542458142726, 60241274678823354422, 60254785469115531301, 60403404119379936262]
                else
                  [60241274545746739205, 60241274807672504902]
            else
              if h < 5 then
                if h < 4 then
                  [60250844682002759718, 69464646569649242174, 69473653768903983158]
                else
                  [60241274545679630341, 60403404119379804741, 60475461713417732613]
              else
                if h < 6 then
                  [60241274545679630342, 60241274670233419829, 60241274670233420582, 60241275907184001797, 69464646569649373198]
                else
                  [60241274670233419830, 60241276740474765318, 60241837491405193222, 60250281869488160814]
          else
            if h < 11 then
              if h < 9 then
                if h < 8 then
                  [60241274542525251598, 60241837482748085253, 63700039046615007398, 69466898369463058446]
                else
                  [60241837491338084358, 60250281869488161318, 60817735422536843310]
              else
                if h < 10 then
                  [60241274542458142734, 60241274542525252102, 60245778269860790325, 60385389720870323782, 60457447314908251654]
                else
                  [60385389720870519814]
            else
              if h < 13 then
                if h < 12 then
                  [60241274542458143238, 60241276766177460750, 60241837482748018742, 60243526342271827982]
                else
                  [60385393019405206021]
              else
                if h < 14 then
                  [60241274545679630350, 60241841880794791942, 60250281869488160821]
                else
                  [60241274670233419838, 62547117816886067302]
        else
          if h < 23 then
            if h < 19 then
              if h < 17 then
                if h < 16 then
                  [60241274545679630854, 60241837482748019750, 70041107321952796686, 70617568074256089142]
                else
                  [60241274542458143494, 60241274670233420342, 60241276740474765830, 60241907851492458502]
              else
                if h < 18 then
                  []
                else
                  [60241276740407656966]
            else
              if h < 21 then
                if h < 20 then
                  [60241274575811248142, 60817735294761566222]
                else
                  [60241837482748084262, 60385389729460519430]
              else
                if h < 22 then
                  [60241274575744139278, 60241274679897358342, 60241276731884831238, 60242118966314663942, 60385389720870322790, 60457447314908250662]
                else
                  [60241276731817722373]
          else
            if h < 27 then
              if h < 25 then
                if h < 24 then
                  [60241276731817722374, 60241276740407657222, 60243526375557824526]
                else
                  [60241274545679515654, 69466898369463123974]
              else
                if h < 26 then
                  [60241274567154204685, 60242118957724729349, 61394196174840266805, 62547117688037048358, 69464646569649374222]
                else
                  [60241274567154204686, 60241276731884831494, 60242118957724729350]
            else
              if h < 29 then
                if h < 28 then
                  [60241276731817722629, 60241837491337969670, 60243526366967889933, 71770489578862936110]
                else
                  [60241276731817722630, 60243526366967889934]
              else
                if h < 30 then
                  [60457447314908252678, 62547117679447113765, 62691232730084016710, 69464646569649242702]
                else
                  [60241274541451509765, 62547117679447113766, 69464646569649438734]
      else
        if h < 46 then
          if h < 38 then
            if h < 34 then
              if h < 32 then
                [60241274541451509766, 60241274542525251622, 60241276731817722382, 60241837482748035077, 60817735328047562766]
              else
                if h < 33 then
                  [60241274541384400901, 60241837482748035078]
                else
                  [60241274541384400902, 60241274542458142758, 60243528531631407630]
            else
              if h < 36 then
                if h < 35 then
                  [60242118957724729358]
                else
                  [60241274541585727502, 60817735319457628173, 62547680491961712678, 71770489578862936118]
              else
                if h < 37 then
                  [60241274532794466308, 60241274567154205198, 60241276731817722638, 60242118957724729862, 60817735319457628174]
                else
                  [60241274532794466309, 60241274545679630374, 60241837482748019270, 60259288931303957062, 60819987119271313421, 62556124878701854757]
          else
            if h < 42 then
              if h < 40 then
                if h < 39 then
                  [60241274532794466310, 60243526366967890446, 60817737484121146118, 62547117679447113774]
                else
                  [60241274541451509774, 60385389720870453830, 60457447314908381702]
              else
                if h < 41 then
                  [60241274670233550886, 60241837482748035086, 60250844682002776070, 62547117679447114278]
                else
                  [60241274541384400910, 60241274541451510278, 60241274567154205454, 60241274610103877686, 60243526341265195022, 60250281741712883750, 60817735319457628430, 60817737484121145870]
            else
              if h < 44 then
                if h < 43 then
                  [60241837482748035590, 60385390820381950725]
                else
                  [60241274541384401414, 60243526341198086158, 60385389733755224582]
              else
                if h < 45 then
                  [60241274684192063494, 60385389720870470150]
                else
                  [60241274532794466317, 60241274601513943093, 60242118957724730373, 62547117679447113781, 69464646616893882374]
        else
          if h < 54 then
            if h < 50 then
              if h < 48 then
                if h < 47 then
                  [60241274532794466318, 60241274541451510534, 60241274601513943094, 60817735319457628686]
                else
                  [60241274532794466821, 60241274541988380710, 60243526332608151565, 60817735293822042126]
              else
                if h < 49 then
                  [60241274532794466822, 60241274541384401670, 60243526332608151566, 60250281869488291878]
                else
                  [60241274532794606630, 60241274542458142774, 60241274542525382662, 60245778201141313589, 60457447314908382214, 60817735293754933262, 63700039184053960741]
            else
              if h < 52 then
                if h < 51 then
                  [60242118957724794885, 69464646578239438862]
                else
                  [60241274542458273798, 60241837482748036101, 60817735293687824398]
              else
                if h < 53 then
                  [60241274532794467077, 60241274532794646542, 60457447314908250693]
                else
                  [60241274532794467078, 60241278939431044102, 60243526366967955470, 60250281800768684085, 60819987093501509646]
          else
            if h < 58 then
              if h < 56 then
                if h < 55 then
                  [60241274601513943102, 60385389720870470662]
                else
                  [60241274545679761414, 60241276731817722406, 60817735285097889805]
              else
                if h < 57 then
                  [60241274532794466830, 60241274601513943606, 60241274670233550902, 60241837482748100613, 60817735285097889806]
                else
                  [60241278930841109509, 60241278930874663942, 60819987084911575053]
            else
              if h < 60 then
                if h < 59 then
                  [60241274567154204718, 60241274671307423782, 60241278930841109510, 60241837491338215430, 60242118957724729382, 60243526332608152078, 60819987084911575054, 69464646608303947790]
                else
                  [60241349299585302533]
              else
                if h < 61 then
                  [60241274670233551910, 60241276731817722662, 60243526366967889966]
                else
                  [60241274532794467086, 60817735285097890062]
    else
      if h < 93 then
        if h < 77 then
          if h < 69 then
            if h < 65 then
              if h < 63 then
                []
              else
                if h < 64 then
                  [60241274541451509798, 60241837482748280838, 60243526332608152334, 60250283931072463398, 60817735285097890566, 60819987084911575310]
                else
                  [60241274670233420390, 60241837482748035110]
            else
              if h < 67 then
                if h < 66 then
                  [60241274541384400934, 60241274670233616422, 61394196106120790069]
                else
                  [60241278930841109518, 60250281766408945710, 60817735285097890318]
              else
                if h < 68 then
                  [60250281869488177190]
                else
                  [60241278930841110022, 60817735319457628206, 60819987084911575566]
          else
            if h < 73 then
              if h < 71 then
                if h < 70 then
                  [60241274532794466341, 62547117542008299558]
                else
                  [60241274532794466342]
              else
                if h < 72 then
                  [60241274542458274822, 60241276731817722422, 60242118966314795014, 60250281740706250790, 60817735285097890574]
                else
                  []
            else
              if h < 75 then
                if h < 74 then
                  [60241276731817853446, 60243526332608217102, 60250281740639141926, 62547117551671836710, 69464646582534144014]
                else
                  [60241274567154204734, 69464646569649389582]
              else
                if h < 76 then
                  [60241274542458143302]
                else
                  [60241274542458339334, 60241274567154335758]
        else
          if h < 85 then
            if h < 81 then
              if h < 79 then
                if h < 78 then
                  [60250281732049207333, 60254785340266512422]
                else
                  [60241274532794466350, 60241276731817853702, 60243526366968021006, 60250281732049207334]
              else
                if h < 80 then
                  [60241274541451509814, 60385389995748229701]
                else
                  [60241274532794466854, 60243526332608151598, 62547117679447244838]
            else
              if h < 83 then
                if h < 82 then
                  [60241274541384400950, 60241274541451640838, 60241837495632920582, 60254785331676577829]
                else
                  [60241276740407657030, 60241278930841175045, 60254785331676577830]
              else
                if h < 84 then
                  [60241274541384531974, 60241837482748281862, 60819987084911640590]
                else
                  []
          else
            if h < 89 then
              if h < 87 then
                if h < 86 then
                  [60241274532794466357, 60241274532794467110, 60241274678823616550, 60241276731884831302, 60245778141011771446, 62547117610727637045]
                else
                  [60241274532794466358, 60241276731817722437, 60250281732049207342, 60817735319457759246]
              else
                if h < 88 then
                  [60241274532794597381, 60241276731817722438]
                else
                  [60241274532794597382, 60241837482748346374, 60250281732049207846, 60252533531862892590, 60817735285097889838]
            else
              if h < 91 then
                if h < 90 then
                  [60245778132421836853, 60250281740639141942, 62547117551134965798]
                else
                  [60241274541385187342, 60241278930841109542, 60245778132421836854, 60254785331676577838, 60819987084911575086]
              else
                if h < 92 then
                  [60241276731817722693, 60313334325855650565]
                else
                  [60254785331676578342]
      else
        if h < 109 then
          if h < 101 then
            if h < 97 then
              if h < 95 then
                if h < 94 then
                  [60241276731817854470, 60243526332608218126, 60250281732049207349, 60250281732049208102, 69464646569649242766, 69608761757725098510]
                else
                  [60241274532794466366, 60242118957724745733, 60250281732049207350, 62547117679447113830]
              else
                if h < 96 then
                  [60241276731817722446, 62547119741031416358]
                else
                  [60241274532794466870, 60241274532794597390, 60241274567154336782, 60241274601514074166, 60243526332608151614, 60826742484352630830]
            else
              if h < 99 then
                if h < 98 then
                  [60241277015352672262, 60254785331676577845]
                else
                  [60241274532794597894, 60241274542525513733, 60241276731817918982, 60241277007232500230, 60243526332608282638, 60245778132421836862, 62547117576367898670]
              else
                if h < 100 then
                  []
                else
                  [60241274542458404869, 60241274567154205262, 60245778132421837366, 60250352100793401382]
          else
            if h < 105 then
              if h < 103 then
                if h < 102 then
                  [60241274532794467126, 60241274541451641862, 60241274542458404870, 60241274567154401294, 60385952670823875078, 60403404119379812870, 61394196045991247926, 61407706836283424805]
                else
                  [60250281732049207358, 60259291130327204421]
              else
                if h < 104 then
                  [60241274532794598150, 60241274541384532998, 62547117550665203750]
                else
                  [60241274581112848390, 60250281732049207862, 60817735285097889854]
            else
              if h < 107 then
                if h < 106 then
                  [60241274541451510342, 60241344910128726022, 61394196037401313333, 62547117550598094886]
                else
                  [60241274541451706374, 60241276740475027462, 60817735285098020878, 61394196037401313334]
              else
                if h < 108 then
                  [60241274532794598405, 60241274541384401478]
                else
                  [60241274532794598406, 60241274541384597510, 60241274683118321702, 60819987084911706126]
        else
          if h < 117 then
            if h < 113 then
              if h < 111 then
                if h < 110 then
                  [60241274542458404878, 60241274670233567270, 60241277015285563910, 60241344901538791429, 61398699637028683829, 62547117542008160293]
                else
                  [60241344901538791430, 62547117542008160294]
              else
                if h < 112 then
                  [60241274532794466885, 60241274542458405382, 60385952670823875590]
                else
                  [60241274532794466886, 60241274532794662917, 60241274541384401734, 60241277006762738182, 60313332135422329606]
            else
              if h < 115 then
                if h < 114 then
                  [60241274532794662918, 60241277006695629317, 61403203236656054325, 62556124749852835878]
                else
                  [60241277006695629318, 61394196037401313342]
              else
                if h < 116 then
                  [60243526332608348166]
                else
                  [60241274532794467141, 60241274532794598414, 60241912249538707461, 60313332126832395013, 61394196037401313846]
          else
            if h < 121 then
              if h < 119 then
                if h < 118 then
                  [60241274532794467142, 60241274572522913806, 60313332126832395014, 62556124741262901285]
                else
                  [60241274532794598918, 60241276740407919110, 60241277006695629573, 60241344901538791438, 60243526332608283662, 60250352100793532422, 62547117542008160302, 62556124741262901286]
              else
                if h < 120 then
                  [60241276731817722470, 60241277839986393094]
                else
                  [60241274532794466894, 60241274532794597414, 60241274542458290182, 60241344901538791942, 60250281740641239078, 62547117542008160806, 62549369341821845550]
            else
              if h < 123 then
                if h < 122 then
                  [60241274532794662926, 60241274546820218885, 60241274575744401422, 60241276731885093382, 62547117550598094902, 62560628340890271781]
                else
                  [60241277006695629326, 60243526332608152142]
              else
                if h < 124 then
                  [60241274532794599174, 60241274532794663430, 60241274546753110021, 60243526332608348174, 60259288939893883462]
                else
                  [60241274546753110022]
  else
    if h < 188 then
      if h < 156 then
        if h < 140 then
          if h < 132 then
            if h < 128 then
              if h < 126 then
                [60241274532794467150, 60241556007771897862, 60241560405817884677, 60313332126832395022, 60817735285097890126, 60819987084911771654, 60889792879135817998, 62547117542008160309, 62547117542008161062, 63700039055204941862]
              else
                if h < 127 then
                  [60241278930841125893, 60242118957724991494, 60817735285098021902, 62547117542008160310, 62556124741262901294]
                else
                  [60259288931303948869, 60817735285097890630, 60889792879135818502, 62547119741031416390]
            else
              if h < 130 then
                if h < 129 then
                  [60241274532794663686, 60241274541384598534, 60241626376515551237, 60250281732049338406, 60259288931303948870, 60385389858309276198, 62556124741262901798, 63123578294311583790]
                else
                  [60241276744769732614, 60241344901538792453, 60259291405205111301, 62551621141635530805, 63700039046615007269]
              else
                if h < 131 then
                  [60241274541451771909, 60817735285097890382, 63700039046615007270]
                else
                  [60241274541451771910, 60241277839919284742, 60241837495633051654, 60817735285098086414, 69465209519602794510]
          else
            if h < 136 then
              if h < 134 then
                if h < 133 then
                  [60241274532794663941, 60241274541384663045, 60241274546753110030, 60241274748616572934, 60241277831463567878, 60241837482748297222, 60254785331676708902, 60259288931303949125, 60331346525341876997]
                else
                  [60241274532794663942, 60241274541384663046, 60241274542458404902, 62556124741262901301]
              else
                if h < 135 then
                  [60241274546753110534, 60241274580106215430, 60241277831396459014, 60241344901538856965, 60385391928550621190, 62547117542008160318]
                else
                  [60241277831329350149, 60243526332608349190]
            else
              if h < 138 then
                if h < 137 then
                  [60241274532794597430, 60241274580039106566, 60241277831329350150, 60243807807584927758, 60259288931303948878, 62547117542008160822]
                else
                  [60241274741100380198, 60241276731817853510, 63709046245869748261, 69464646580386660366]
              else
                if h < 139 then
                  [60243526379852791814, 63700039046615007278]
                else
                  [60241274541451771918, 60385389730533999110]
        else
          if h < 148 then
            if h < 144 then
              if h < 142 then
                if h < 141 then
                  [60241274532794598438, 60241277831329350405, 60245778132421967926, 63700039046615007782]
                else
                  [60241274532794663950, 60241274541384663054, 60241274541451772422, 60241276744702624262]
              else
                if h < 143 then
                  [60241274541418217990, 60241276731817869830, 60241344901538791462, 60243526332608233486]
                else
                  [60241274532794664454, 60241274541384663558, 60243526341198348302, 69464646569649405966]
            else
              if h < 146 then
                if h < 145 then
                  [60241274532794466918, 60241274580039106574, 60241277831329350158, 60250281732049338422]
                else
                  [60241274532794662950, 60241274567154352142, 63700039046615007285]
              else
                if h < 147 then
                  [60241277006695629350, 60385391928483512838, 60385394118916834822, 60817735285098022926, 60817735332342530054]
                else
                  [60241274571516280846, 60250281732049223718]
          else
            if h < 152 then
              if h < 150 then
                if h < 149 then
                  [60241274541384663814, 60250281732049339430]
                else
                  [60241274532794467174, 60241274571449171982, 60313332126832395046, 60385391919960687110]
              else
                if h < 151 then
                  [60241274541451657222, 60385391919893578245]
                else
                  [60241274542458535942, 60243526371262857230, 60254785331676594214, 60385391919893578246, 60817735293688086542]
            else
              if h < 154 then
                if h < 153 then
                  [60241274541384548358, 60250281732049207910, 62547117542008160838]
                else
                  [60241274545746477061, 60250281732049403942]
              else
                if h < 155 then
                  [60241274545746477062]
                else
                  [60241274545679368197, 60385391919893578501]
      else
        if h < 172 then
          if h < 164 then
            if h < 160 then
              if h < 158 then
                if h < 157 then
                  [60241274532794598454, 60241274532794600462, 60241274532794613765, 60241274545679368198, 60241274546753110054, 61394196037401444406]
                else
                  [60241274532794613766, 60241344901540888582, 60313332126832397062, 62547117542008161094]
              else
                if h < 159 then
                  [69464646707088195630]
                else
                  [60241841889384464390, 60385391919893578254, 60817735323752595470]
            else
              if h < 162 then
                if h < 161 then
                  [60241274532794466934, 60259288931303948902, 62547117542008291366]
                else
                  [60241274532794662966, 60241275640896029446]
              else
                if h < 163 then
                  [60241274532794597958, 60241274545746477070, 60241275632440312582, 60241907860082130950]
                else
                  [60241274541451771942, 60241841880794529797, 60241841880828084230, 60250281732049223734]
          else
            if h < 168 then
              if h < 166 then
                if h < 165 then
                  [60241274545679368206, 60241274545746477574, 60241277006695760390, 60241841880794529798, 60385389755230061070]
                else
                  [60241274532794613774, 60241274532794663974, 60241274541384663078, 60241275632306094853, 60250281732049354758]
              else
                if h < 167 then
                  [60241274545679368710, 60241275632306094854, 60241837620186972198, 60241907851492196357, 60243526345493053454, 60403406318403060229, 69464646707088195638]
                else
                  [60241274532794598214, 60241274532794614278, 60241907851492196358, 60243526332608299022, 60250281732049224742, 60313332126832526086]
            else
              if h < 170 then
                if h < 169 then
                  [60241277831329350182, 62556124741263032358, 62565131940517642822]
                else
                  [60241274740026638374, 60254785331676725254, 60385389729527366150, 69464646579312918542]
              else
                if h < 171 then
                  [60241274679964205062, 60385389729493811718]
                else
                  [60241274545679368966, 60241556016361308166, 60385389729460257286, 60385391919893579270]
        else
          if h < 180 then
            if h < 176 then
              if h < 174 then
                if h < 173 then
                  [60241274532794614534, 60241274541384549382, 60241274679897096198, 60241841880794529806, 63700039046615007814]
                else
                  [60250281740639404070]
              else
                if h < 175 then
                  [60241274546753241094, 60241275632306094862, 60241841880794530310, 60817735297982791694, 60817736384609517838, 62547117542008160358]
                else
                  [60241556007771373573, 60241907851492196366, 60385389720870322693, 60817735285098037262]
            else
              if h < 178 then
                if h < 177 then
                  [60241274532794614789, 60241556007771373574, 60385389720870322694, 60385389729460257542, 60817736384609518342, 62547117542008291382]
                else
                  [60241274532794614790, 60241274541384613894, 60241277006695629381, 60241837492411695110, 60241907851492196870]
              else
                if h < 179 then
                  [60243807807585058822, 60259288931304079942]
                else
                  []
          else
            if h < 184 then
              if h < 182 then
                if h < 181 then
                  [60250281879151837190, 60313332126832395077, 60385389720870322949, 62547117542008292390, 63700039046615138342]
                else
                  [60241274532794679301, 60241274541384663094, 60241274541451902982, 60385389720870322950, 69464646612598915086]
              else
                if h < 183 then
                  [60241274532794598982, 60241274532794679302, 62556124741262901350, 69464646638368718878]
                else
                  [60241274541384794118, 60241841880794530821, 60385391919893578278]
            else
              if h < 186 then
                if h < 185 then
                  [60241556007771373582, 60243526332608364550, 60385389720870322702, 62547117542008160870]
                else
                  [60241274532794614798, 60250281732049355782, 62547117542008356902, 69464646604008980493]
              else
                if h < 187 then
                  [60241274545746477094, 60241277831329481222, 60241556007771374086, 60241907851492197381, 60385394118916965382, 60387641520684007950, 69464646604008980494]
                else
                  [60241274532794615302, 60241274532794663494, 60241274808209244742, 60403404127969739270, 62556124741262917670, 69466898403822665741]
    else
      if h < 219 then
        if h < 203 then
          if h < 195 then
            if h < 191 then
              if h < 189 then
                [60241274545679368230, 60241841880794595333]
              else
                if h < 190 then
                  [60241274532794613798, 60385389720870322958]
                else
                  [60241274532794679310, 60250281732049420294, 62547117542008160374, 62565131940517642342]
            else
              if h < 193 then
                if h < 192 then
                  [60241907851492261893, 60403404119379804677, 60961850473173746438, 69464648768672498190]
                else
                  [60241274532794679814, 60403404119379804678]
              else
                if h < 194 then
                  []
                else
                  [60961850473173746190, 63700039046615007334]
          else
            if h < 199 then
              if h < 197 then
                if h < 196 then
                  [60241556007771374597, 70041107356312403981]
                else
                  [60241274544605626382, 60241274747542831142, 60241841880794529830, 60250281744934109222, 60385389720870323718, 60403404119379804933, 69464646604008981006]
              else
                if h < 198 then
                  [60250281732049354790]
                else
                  [60241274816262308422, 60241275632306094886]
            else
              if h < 201 then
                if h < 200 then
                  [60241277831329350213, 60241839681771274758, 60241907851492196390, 60313335425367278085, 69464646578306285582]
                else
                  [60241274738952896549, 60403404119379804686]
              else
                if h < 202 then
                  [60241274532794680325, 60241274738952896550, 60385389720870323974, 60385391919893709318, 69464646578239176718]
                else
                  [60241274807672373829, 60241837517107757070, 69464646604008980510]
        else
          if h < 211 then
            if h < 207 then
              if h < 205 then
                if h < 204 then
                  [60241274541384795142, 60241274807672373830, 69466898378052861966]
                else
                  [60241274545679368246, 60241274545746608134, 60241274679897096230, 60245778338580267045]
              else
                if h < 206 then
                  [60241274532794613814, 62547117550598357030, 62556124741263048710, 69464646569649242125]
                else
                  [60241274545679499270, 69464646569649242126, 69464646638368718902]
            else
              if h < 209 then
                if h < 208 then
                  [60241274541384663622, 60241274671374270502, 60241274807672374085, 60241837491405062150, 69466898369462927373]
                else
                  [60241274541384859654, 60241556007771373606, 60250281938207637541, 60385389720870322726, 69466898369462927374]
              else
                if h < 210 then
                  [60241274532794614822, 60241274671307161638, 60241274738952896558, 60241837491337953286, 60241841889384595462]
                else
                  []
          else
            if h < 215 then
              if h < 213 then
                if h < 212 then
                  [60241274738952897062, 60241274807672373838, 70041107330542600206]
                else
                  [60241274541386760230, 60241907860082262022, 60403404119379805702, 62547117689110790150]
              else
                if h < 214 then
                  [60241837482748018693, 60385389720870322982]
                else
                  [60241274532794679334, 60241837482748018694, 60241907851494293510, 60385391919893578309, 60457449513931506181]
            else
              if h < 217 then
                if h < 216 then
                  [70041107321952665613]
                else
                  [60241274738952896565, 60241275632306225926, 60394396920125063718, 69464646569649242638, 70041107321952665614]
              else
                if h < 218 then
                  [60250281870561902630, 70043359121766350861]
                else
                  [60259289206181855813, 69464646604008980526, 69466898369462927886]
      else
        if h < 235 then
          if h < 227 then
            if h < 223 then
              if h < 221 then
                if h < 220 then
                  []
                else
                  [60254785331676610598, 61394196243559743525]
              else
                if h < 222 then
                  [69464646569649242894, 70041107321952665870]
                else
                  [60241837482748018702, 69464646569649242142]
            else
              if h < 225 then
                if h < 224 then
                  [60241274546753372165, 70041107321952666374]
                else
                  [60241837482748019206, 60244089282561703950, 60385389720870322742, 60403404119379804710, 69466898369462927390]
              else
                if h < 226 then
                  [60241274671307161654, 60241276741548507142]
                else
                  [60241274545679500294, 60241276869256675878, 60241278106207257093, 60242118957725253638, 60242123355771240453, 60385389720870453766, 69469150169276612638, 70041107321952666126]
          else
            if h < 231 then
              if h < 229 then
                if h < 228 then
                  [60241837492411826182]
                else
                  [60245778132421869622, 62547117554893062182]
              else
                if h < 230 then
                  [60241274704593158190, 60241275632306094917, 60241837482748019462, 60241837491337954310, 60242189326468907013, 60313333226344022789, 62547117542008307750]
                else
                  [60241274545679368774]
            else
              if h < 233 then
                if h < 232 then
                  [60241274532794614342, 60241274545679564806, 60385389720870454022]
                else
                  [60241841880794546181, 60818298235051442190, 70041107321952665630]
              else
                if h < 234 then
                  [60241274603661426742, 60241837482748019717, 69466898369462992910]
                else
                  [60241274678890463270, 60241837482748019718, 60241837491338018822, 61394196037401313462]
        else
          if h < 243 then
            if h < 239 then
              if h < 237 then
                if h < 236 then
                  [60241274807672373862, 60241907851492212741, 60385389729460257350, 60457447323498185222]
                else
                  [60241274580039368710, 60241274678823354406, 60385389720870454278, 69464646604009111566]
              else
                if h < 238 then
                  [60241276741481398790]
                else
                  [60241837482748084229, 69464646569649242158]
            else
              if h < 241 then
                if h < 240 then
                  [60241837482748084230, 60385389720870322757, 60457447314908250629]
                else
                  [60241274576817881102, 60241274670233419813, 60385389720870322758, 60457447314908250630, 62547117748166590501, 69466898369462927406]
              else
                if h < 242 then
                  [60241274670233419814, 60244089282561769478, 60385392194771485189]
                else
                  [60241837482748019726, 60403404119379935750, 70617568074256089118]
          else
            if h < 247 then
              if h < 245 then
                if h < 244 then
                  [60243526341198610446, 62547117816886067782]
                else
                  [60241556007771389957, 60241837482748020230, 60250281878078095398, 60385389720870323013, 60457447314908250885]
              else
                if h < 246 then
                  []
                else
                  [60241837482748018726, 60385389720870454790, 69464646569649242166, 69473653768903983150]
            else
              if h < 249 then
                if h < 248 then
                  [60241837482748084238]
                else
                  [60241274532794467022, 60250281869488160805, 60385389720870322766, 60457447314908250638, 62691232730084016678, 70041107321952665646]
              else
                if h < 250 then
                  [60241274542525251589, 60241274571449434126, 60241274670233419822, 60241837482748084742, 60250281869488160806, 62547117680520855590]
                else
                  [60241274542525251590, 69469150169276612662]

def bHas (f : Nat → List Nat) (x : Nat) : Bool :=
  (f (x % 251)).elem x

def bAll (f : Nat → List Nat) (p : Nat → Bool) : Bool :=
  (List.range 251).all fun h => (f h).all p

theorem bAll_has {f : Nat → List Nat} {p : Nat → Bool} (h : bAll f p = true)
    {x : Nat} (hx : bHas f x = true) : p x = true := by
  have hlt : x % 251 < 251 := Nat.mod_lt x (by decide)
  have hall := List.all_eq_true.mp h _ (List.mem_range.mpr hlt)
  exact List.all_eq_true.mp hall _ (List.elem_iff.mp hx)

def stepCheckCode (dst : Nat → List Nat) (sc : Nat) : Bool :=
  let m := sc >>> 2
  let c := sc &&& 3
  bHas dst sc &&
  (List.range 64).all fun a =>
    if !m.testBit a then true else
    ((if c < 2 then bHas dst (((m ||| (1 <<< (63 ^^^ a))) <<< 2) ||| (c + 1)) else true) &&
     (List.range 64).all fun b =>
       if !m.testBit b then true else
       bHas dst (((m ||| (1 <<< (a &&& b))) <<< 2) ||| c) &&
       bHas dst (((m ||| (1 <<< (a ||| b))) <<< 2) ||| c))

def checkOne (ta tb tc sc : Nat) : Bool :=
  let m := sc >>> 2
  let c := sc &&& 3
  let ma := !m.testBit ta
  let mb := !m.testBit tb
  let mc := !m.testBit tc
  if !ma && !mb && !mc then false
  else
    let tgt := if ma then ta else if mb then tb else tc
    if (ma && (ta != tgt)) || (mb && (tb != tgt)) || (mc && (tc != tgt)) then true
    else
      !((List.range 64).any fun a =>
        m.testBit a &&
        ((c < 2 && ((63 ^^^ a) == tgt)) ||
         (List.range 64).any fun b =>
           m.testBit b && (((a &&& b) == tgt) || ((a ||| b) == tgt))))

theorem bAll_01 : bAll bT0 (stepCheckCode bT1) = true := by decide +kernel
theorem bAll_12 : bAll bT1 (stepCheckCode bT2) = true := by decide +kernel
theorem bAll_23 : bAll bT2 (stepCheckCode bT3) = true := by decide +kernel
theorem bAll_34 : bAll bT3 (stepCheckCode bT4) = true := by decide +kernel
theorem bAll_target : bAll bT4 (checkOne 28 40 46) = true := by decide +kernel

theorem init_code_ok : bHas bT0 ((setMask [62, 60, 56, 48, 32, 0, 63] <<< 2) ||| 0) = true := by
  decide +kernel

def bTk (k : Nat) : Nat → List Nat :=
  match k with | 0 => bT0 | 1 => bT1 | 2 => bT2 | 3 => bT3 | _ => bT4

theorem bTk_step {k : Nat} (hk : k < 4) {sc : Nat} (hsc : bHas (bTk k) sc = true) :
    stepCheckCode (bTk (k + 1)) sc = true := by
  match k with
  | 0 => exact bAll_has bAll_01 hsc
  | 1 => exact bAll_has bAll_12 hsc
  | 2 => exact bAll_has bAll_23 hsc
  | 3 => exact bAll_has bAll_34 hsc
  | k + 4 => omega

private theorem setMask_append (vs : List Nat) (v : Nat) :
    setMask (vs ++ [v]) = setMask vs ||| (1 <<< v) := by
  simp [setMask, List.foldl_append]

private theorem testBit_fold_mem (xs : List Nat) (acc : Nat) (x : Nat)
    (h : acc.testBit x = true ∨ x ∈ xs) :
    (xs.foldl (fun m v => m ||| (1 <<< v)) acc).testBit x = true := by
  induction xs generalizing acc with
  | nil => rcases h with h | h; exact h; cases h
  | cons y ys ih =>
    apply ih
    rcases h with h | h
    · left; simp [Nat.testBit_or, h]
    · rcases List.mem_cons.mp h with rfl | h
      · left; simp [Nat.testBit_or, Nat.testBit_shiftLeft]
      · right; exact h

private theorem testBit_setMask_of_mem {vs : List Nat} {v : Nat} (hv : v ∈ vs) :
    (setMask vs).testBit v = true :=
  testBit_fold_mem vs 0 v (Or.inr hv)

private theorem testBit_setMask_getD (vs : List Nat) (h0 : 0 ∈ vs) (i : Nat) :
    (setMask vs).testBit (vs.getD i 0) = true := by
  have hmem : vs.getD i 0 ∈ vs := by
    simp only [List.getD]
    cases hv : vs[i]? with
    | none => exact h0
    | some v => exact List.mem_of_getElem? hv
  exact testBit_setMask_of_mem hmem

private theorem setMask_or_id {vs : List Nat} {v : Nat} (hv : (setMask vs).testBit v = true) :
    setMask vs ||| (1 <<< v) = setMask vs := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hvk : v = k
  · subst hvk; simp [hv]
  · by_cases hle : v ≤ k
    · have h1 : (1 : Nat).testBit (k - v) = false := by
        cases hkv : k - v with
        | zero => omega
        | succ m => simp [Nat.testBit_succ]
      simp [hle, h1]
    · simp [hle]

private theorem pack_shift_or (m c : Nat) (hc : c ≤ 2) :
    (((m <<< 2) ||| c) >>> 2 = m) ∧ (((m <<< 2) ||| c) &&& 3 = c) := by
  have hc4 : c < 4 := by omega
  have hshift : ((m <<< 2) ||| c) >>> 2 = m := by
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft]
    have hc_bit : c.testBit (2 + k) = false := by
      apply Nat.testBit_eq_false_of_lt
      calc c < 4 := hc4
        _ = 2 ^ 2 := rfl
        _ ≤ 2 ^ (2 + k) := Nat.pow_le_pow_right (by decide) (by omega)
    have hge : 2 ≤ 2 + k := by omega
    have hsub : 2 + k - 2 = k := by omega
    simp [hge, hsub, hc_bit]
  have hand : ((m <<< 2) ||| c) &&& 3 = c := by
    apply Nat.eq_of_testBit_eq; intro k
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hk : k < 2
    · have h3 : (3 : Nat).testBit k = true := by
        rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> decide
      have hfalse : ¬ (2 ≤ k) := by omega
      simp [hfalse, h3]
    · have hc_k : c.testBit k = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hc4 (by
        calc 4 = 2 ^ 2 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)))
      have h3 : (3 : Nat).testBit k = false := Nat.testBit_eq_false_of_lt (by
        calc 3 < 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega))
      simp [h3, hc_k]
  exact ⟨hshift, hand⟩

private theorem getD_lt_32 (vs : List Nat) (hvs : ∀ v ∈ vs, v < 64) (i : Nat) :
    vs.getD i 0 < 64 := by
  simp only [List.getD]
  cases hv : vs[i]? with
  | none => decide
  | some v => exact hvs v (List.mem_of_getElem? hv)

theorem gateMask_lt (vs : List Nat) (g : Gate) (hvs : ∀ v ∈ vs, v < 64)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    gateMask vs g < 64 := by
  rcases hfan with ⟨hop, _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases hgop : g.op <;> simp only [hgop, reduceCtorEq, false_or, or_false] at hop
  · match hi : g.inputs with
    | [] => simp [gateMask, hgop, hi]
    | [a] => simpa [gateMask, hgop, hi] using getD_lt_32 vs hvs a
    | a :: b :: _ =>
      have ha := getD_lt_32 vs hvs a
      simp only [gateMask, hgop, hi]
      exact Nat.lt_of_le_of_lt Nat.and_le_left ha
  · match hi : g.inputs with
    | [] => simp [gateMask, hgop, hi]
    | [a] => simpa [gateMask, hgop, hi] using getD_lt_32 vs hvs a
    | a :: b :: _ =>
      have ha := getD_lt_32 vs hvs a; have hb := getD_lt_32 vs hvs b
      simp only [gateMask, hgop, hi]
      exact Nat.or_lt_two_pow (n := 6) ha hb
  · match hi : g.inputs with
    | [] => simp [gateMask, hgop, hi]
    | a :: _ =>
      have ha := getD_lt_32 vs hvs a
      simp only [gateMask, hgop, hi]
      exact Nat.xor_lt_two_pow (n := 6) (by decide) ha

theorem foldMasks_inv (gs : List Gate) (vs : List Nat)
    (h0 : 0 ∈ vs) (h31 : 63 ∈ vs) (hvs : ∀ v ∈ vs, v < 64)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    0 ∈ foldMasks gs vs ∧ 63 ∈ foldMasks gs vs ∧ (∀ v ∈ foldMasks gs vs, v < 64) := by
  induction gs generalizing vs with
  | nil => exact ⟨h0, h31, hvs⟩
  | cons g gs ih =>
    apply ih (vs ++ [gateMask vs g])
    · exact List.mem_append_left _ h0
    · exact List.mem_append_left _ h31
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hvs v hv
      · rw [List.mem_singleton.mp hv]; exact gateMask_lt vs g hvs (hfan g List.mem_cons_self)
    · intro g' hg'; exact hfan g' (List.mem_cons_of_mem _ hg')

private theorem gate_eval_bit (vs : List Nat) (w : List Bool) (g : Gate) (t : Fin 6)
    (hw : ∀ k, w.getD k false = (vs.getD k 0).testBit t.val)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (gateMask vs g).testBit t.val := by
  have ht : t.val < 6 := t.isLt
  have h31 : (63 : Nat).testBit t.val = true := by
    rcases (show t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨ t.val = 4 ∨ t.val = 5 by omega) with
      h | h | h | h | h | h <;> rw [h] <;> decide
  rcases hfan with ⟨hop, hlen⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases hgop : g.op <;> simp only [hgop, reduceCtorEq, false_or, or_false] at hop
  · match hi : g.inputs with
    | [] => simp [GateOp.eval, gateMask, hgop, hi, h31]
    | [a] => simpa [GateOp.eval, gateMask, hgop, hi] using hw a
    | a :: b :: rest =>
      simp only [hi, List.length_cons] at hlen
      have hr : rest = [] := List.length_eq_zero_iff.mp (by omega)
      subst hr
      have ha := hw a; have hb := hw b
      simpa [GateOp.eval, gateMask, hgop, hi, Nat.testBit_and] using congrArg₂ (· && ·) ha hb
  · match hi : g.inputs with
    | [] => simp [GateOp.eval, gateMask, hgop, hi]
    | [a] => simpa [GateOp.eval, gateMask, hgop, hi] using hw a
    | a :: b :: rest =>
      simp only [hi, List.length_cons] at hlen
      have hr : rest = [] := List.length_eq_zero_iff.mp (by omega)
      subst hr
      have ha := hw a; have hb := hw b
      simpa [GateOp.eval, gateMask, hgop, hi, Nat.testBit_or] using congrArg₂ (· || ·) ha hb
  · match hi : g.inputs with
    | [] => simp [GateOp.eval, gateMask, hgop, hi, h31]
    | a :: _ =>
      have ha := hw a
      simpa [GateOp.eval, gateMask, hgop, hi, Nat.testBit_xor, h31] using congrArg not ha

theorem foldl_wires_mask (gs : List Gate) (vs : List Nat) (ws : Fin 6 → List Bool)
    (hlen : ∀ t, (ws t).length = vs.length)
    (hw : ∀ t : Fin 6, ∀ k, (ws t).getD k false = (vs.getD k 0).testBit t.val)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ t : Fin 6, ∀ k,
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (ws t)).getD k false =
      ((foldMasks gs vs).getD k 0).testBit t.val := by
  induction gs generalizing vs ws with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (vs ++ [gateMask vs g]) (fun t' => ws t' ++ [g.op.eval (g.inputs.map fun i => (ws t').getD i false)])
    · intro t'; simp [hlen t']
    · intro t' k'
      by_cases hk : k' < vs.length
      · have hkw : k' < (ws t').length := by rw [hlen t']; exact hk
        simp only [List.getD, List.getElem?_append_left hk, List.getElem?_append_left hkw]
        simpa [List.getD] using hw t' k'
      · by_cases heq : k' = vs.length
        · subst heq
          have heqw : (ws t').length = vs.length := hlen t'
          simp [List.getD, heqw]
          exact gate_eval_bit vs (ws t') g t' (hw t') (hfan g List.mem_cons_self)
        · have hgt : vs.length + 1 ≤ k' := by omega
          have hgtw : (ws t').length + 1 ≤ k' := by rw [hlen t']; exact hgt
          simp [List.getD, List.getElem?_eq_none (by simp; omega : (vs ++ [gateMask vs g]).length ≤ k'),
            List.getElem?_eq_none (by simp; omega : (ws t' ++ [_]).length ≤ k')]
    · intro g' hg'; exact hfan g' (List.mem_cons_of_mem _ hg')

private def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

private theorem step_one_gate (dst : Nat → List Nat) (vs : List Nat) (c : Nat)
    (h0 : 0 ∈ vs) (h31 : 63 ∈ vs) (hvs : ∀ v ∈ vs, v < 64) (hc2 : c ≤ 2)
    (hstep : stepCheckCode dst ((setMask vs <<< 2) ||| c) = true)
    (g : Gate) (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hc_next : c + (if isNotOp g.op then 1 else 0) ≤ 2) :
    bHas dst ((setMask (vs ++ [gateMask vs g]) <<< 2) ||| (c + (if isNotOp g.op then 1 else 0))) = true := by
  have ⟨hm, hc⟩ := pack_shift_or (setMask vs) c hc2
  have hstay : bHas dst ((setMask vs <<< 2) ||| c) = true := (Bool.and_eq_true _ _ |>.mp hstep).1
  have hallA := List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp hstep).2
  have hbit : ∀ v ∈ vs, (setMask vs).testBit v = true := fun _ hv => testBit_setMask_of_mem hv
  have stepA := fun (a : Nat) (ha : a < 64) (hma : (setMask vs).testBit a = true) => by
    have ha' := hallA a (List.mem_range.mpr ha)
    rw [hm, hc] at ha'
    simp only [hma, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ha'
    exact Bool.and_eq_true _ _ |>.mp ha'
  rw [setMask_append]
  rcases hfan with ⟨hop, _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  cases hgop : g.op <;> simp only [hgop, reduceCtorEq, false_or, or_false] at hop
  · simp only [isNotOp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    match hi : g.inputs with
    | [] =>
      simp only [gateMask, hgop, hi, setMask_or_id (hbit 63 h31)]; exact hstay
    | [a] =>
      simp only [gateMask, hgop, hi, setMask_or_id (testBit_setMask_getD vs h0 a)]; exact hstay
    | a :: b :: _ =>
      have ha := getD_lt_32 vs hvs a; have hb := getD_lt_32 vs hvs b
      have hba := testBit_setMask_getD vs h0 a; have hbb := testBit_setMask_getD vs h0 b
      have hallB := List.all_eq_true.mp (stepA _ ha hba).2
      have hb' := hallB _ (List.mem_range.mpr hb)
      simp only [hbb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb'
      simpa [gateMask, hgop, hi] using (Bool.and_eq_true _ _ |>.mp hb').1
  · simp only [isNotOp, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    match hi : g.inputs with
    | [] =>
      simp only [gateMask, hgop, hi, setMask_or_id (hbit 0 h0)]; exact hstay
    | [a] =>
      simp only [gateMask, hgop, hi, setMask_or_id (testBit_setMask_getD vs h0 a)]; exact hstay
    | a :: b :: _ =>
      have ha := getD_lt_32 vs hvs a; have hb := getD_lt_32 vs hvs b
      have hba := testBit_setMask_getD vs h0 a; have hbb := testBit_setMask_getD vs h0 b
      have hallB := List.all_eq_true.mp (stepA _ ha hba).2
      have hb' := hallB _ (List.mem_range.mpr hb)
      simp only [hbb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hb'
      simpa [gateMask, hgop, hi] using (Bool.and_eq_true _ _ |>.mp hb').2
  · simp only [hgop, isNotOp, ↓reduceIte] at hc_next ⊢
    have hclt : c < 2 := by omega
    match hi : g.inputs with
    | [] =>
      have hnot0 := (stepA 0 (by decide) (hbit 0 h0)).1
      simp only [hclt, ↓reduceIte] at hnot0
      simpa [gateMask, hgop, hi] using hnot0
    | a :: _ =>
      have ha := getD_lt_32 vs hvs a
      have hba := testBit_setMask_getD vs h0 a
      have hnota := (stepA _ ha hba).1
      simp only [hclt, ↓reduceIte] at hnota
      simpa [gateMask, hgop, hi] using hnota

private def notC (gs : List Gate) : Nat :=
  (gs.filter fun g => isNotOp g.op).length

private theorem notC_append (gs : List Gate) (g : Gate) :
    notC (gs ++ [g]) = notC gs + (if isNotOp g.op then 1 else 0) := by
  simp only [notC, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases g.op <;> simp [isNotOp]

private theorem notCount_eq_notC (D : Circuit) : PEqualNP.NotBracket.notCount D = notC D.gates := by
  unfold PEqualNP.NotBracket.notCount notC
  congr 2; funext g
  cases g.op <;> rfl

private theorem init_inv :
    0 ∈ [62, 60, 56, 48, 32, 0, 63] ∧ 63 ∈ [62, 60, 56, 48, 32, 0, 63] ∧
    ∀ v ∈ [62, 60, 56, 48, 32, 0, 63], v < 64 := by decide

theorem foldMasks_in_bTk (gs : List Gate) (hlen : gs.length ≤ 4)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hnot : notC gs ≤ 2) :
    bHas (bTk gs.length) ((setMask (foldMasks gs [62, 60, 56, 48, 32, 0, 63]) <<< 2) ||| notC gs) = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [bTk, foldMasks, notC] using init_code_ok
  | append_singleton gs g ih =>
    simp only [List.length_append, List.length_singleton] at hlen ⊢
    rw [notC_append] at hnot ⊢
    have hfan_gs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hfan_g := hfan g (List.mem_append_right _ List.mem_cons_self)
    have hsc := ih (by omega) hfan_gs (by omega)
    have hstep := bTk_step (k := gs.length) (by omega) hsc
    have ⟨h0, h31, hvs⟩ := foldMasks_inv gs [62, 60, 56, 48, 32, 0, 63] init_inv.1 init_inv.2.1 init_inv.2.2 hfan_gs
    have hf : foldMasks (gs ++ [g]) [62, 60, 56, 48, 32, 0, 63] =
        foldMasks gs [62, 60, 56, 48, 32, 0, 63] ++ [gateMask (foldMasks gs [62, 60, 56, 48, 32, 0, 63]) g] := by
      simp [foldMasks, List.foldl_append]
    rw [hf]
    exact step_one_gate (bTk (gs.length + 1)) (foldMasks gs [62, 60, 56, 48, 32, 0, 63]) (notC gs)
      h0 h31 hvs (by omega) hstep g hfan_g hnot

private theorem not_mem_of_not_testBit {vs : List Nat} {v : Nat} (hb : (setMask vs).testBit v = false) :
    v ∉ vs := fun h => by
  have := testBit_setMask_of_mem h; rw [this] at hb; exact Bool.noConfusion hb

private theorem eq_of_testBit_5 {x y : Nat} (hx : x < 64) (hy : y < 64)
    (h : ∀ t : Fin 6, x.testBit t.val = y.testBit t.val) : x = y := by
  apply Nat.eq_of_testBit_eq; intro k
  by_cases hk : k < 6
  · exact h ⟨k, hk⟩
  · have h32 : 64 ≤ 2 ^ k := by
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx h32),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hy h32)]

theorem no_triple_in_5_gates (ta tb tc : Nat)
    (hta : ta < 64) (htb : tb < 64) (htc : tc < 64)
    (hchk : bAll bT4 (checkOne ta tb tc) = true) :
    ∀ (D : Circuit) (p q r : Fin (7 + D.size)),
      PEqualNP.MetaComplexity.FanInTwo D →
      notC D.gates ≤ 2 → D.size ≤ 5 →
      ¬ (∀ t : Fin 6,
        let w := D.wires (xsOf t)
        w.getD p.val false = ta.testBit t.val ∧
        w.getD q.val false = tb.testBit t.val ∧
        w.getD r.val false = tc.testBit t.val) := by
  intro D p q r hfan hnot hsize hmatch
  have hfan' : ∀ g ∈ D.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := hfan
  have hinit_len : ∀ t : Fin 6, (xsOf t).length = ([62, 60, 56, 48, 32, 0, 63] : List Nat).length := fun _ => by simp [xsOf, xsOfN]
  have hinit_all : (List.range 6).all (fun t => (List.range 7).all (fun k =>
      (xsOfN t).getD k false == (([62, 60, 56, 48, 32, 0, 63] : List Nat).getD k 0).testBit t)) = true := by decide +kernel
  have hinit_bit : ∀ t : Fin 6, ∀ k, (xsOf t).getD k false = (([62, 60, 56, 48, 32, 0, 63] : List Nat).getD k 0).testBit t.val := by
    intro t k
    by_cases hk : k < 7
    · have h1 := List.all_eq_true.mp hinit_all t.val (List.mem_range.mpr t.isLt)
      have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr hk)
      exact beq_iff_eq.mp h2
    · simp [List.getD, List.getElem?_eq_none (by simp [xsOf, xsOfN]; omega : (xsOf t).length ≤ k),
        List.getElem?_eq_none (by simp; omega : ([62, 60, 56, 48, 32, 0, 63] : List Nat).length ≤ k)]
  have hwm := foldl_wires_mask D.gates [62, 60, 56, 48, 32, 0, 63] xsOf hinit_len hinit_bit hfan'
  set vsF := foldMasks D.gates [62, 60, 56, 48, 32, 0, 63]
  have ⟨h0F, _, hvsF⟩ := foldMasks_inv D.gates [62, 60, 56, 48, 32, 0, 63] init_inv.1 init_inv.2.1 init_inv.2.2 hfan'
  have hp_eq : vsF.getD p.val 0 = ta :=
    eq_of_testBit_5 (getD_lt_32 vsF hvsF p.val) hta fun t => by
      have := (hwm t p.val).symm.trans (hmatch t).1; simpa [Circuit.wires] using this
  have hq_eq : vsF.getD q.val 0 = tb :=
    eq_of_testBit_5 (getD_lt_32 vsF hvsF q.val) htb fun t => by
      have := (hwm t q.val).symm.trans (hmatch t).2.1; simpa [Circuit.wires] using this
  have hr_eq : vsF.getD r.val 0 = tc :=
    eq_of_testBit_5 (getD_lt_32 vsF hvsF r.val) htc fun t => by
      have := (hwm t r.val).symm.trans (hmatch t).2.2; simpa [Circuit.wires] using this
  have hta_in : (setMask vsF).testBit ta = true := hp_eq ▸ testBit_setMask_getD vsF h0F p.val
  have htb_in : (setMask vsF).testBit tb = true := hq_eq ▸ testBit_setMask_getD vsF h0F q.val
  have htc_in : (setMask vsF).testBit tc = true := hr_eq ▸ testBit_setMask_getD vsF h0F r.val
  change D.gates.length ≤ 5 at hsize
  by_cases h4 : D.gates.length ≤ 4
  · have hmemk := foldMasks_in_bTk D.gates h4 hfan' hnot

    have hmem4 : bHas bT4 ((setMask vsF <<< 2) ||| notC D.gates) = true := by
      have step_up : ∀ k, k ≤ 4 → ∀ sc, bHas (bTk k) sc = true → bHas bT4 sc = true := by
        intro k hk sc hsc
        have aux : ∀ d, k + d ≤ 4 → bHas (bTk (k + d)) sc = true := by
          intro d; induction d with
          | zero => intro _; exact hsc
          | succ d ih =>
            intro hd
            have := bTk_step (k := k + d) (by omega) (ih (by omega))
            exact (Bool.and_eq_true _ _ |>.mp this).1
        simpa [bTk, Nat.add_sub_cancel' hk] using aux (4 - k) (by omega)
      exact step_up D.gates.length h4 _ hmemk
    have hc1 := bAll_has hchk hmem4
    have ⟨hm, _⟩ := pack_shift_or (setMask vsF) (notC D.gates) hnot
    simp only [checkOne, hm, hta_in, htb_in, htc_in] at hc1
    exact Bool.noConfusion hc1
  · have hlen5 : D.gates.length = 5 := by omega
    have hrev : ∃ gs4 g4, D.gates = gs4 ++ [g4] := by
      cases hr : D.gates.reverse with
      | nil => exact absurd (congrArg List.length hr) (by simp [hlen5])
      | cons g4 gs4r =>
        refine ⟨gs4r.reverse, g4, ?_⟩
        rw [← List.reverse_reverse D.gates, hr, List.reverse_cons]
    rcases hrev with ⟨gs4, g4, hgs⟩
    rw [hgs] at hfan' hnot hlen5
    simp only [List.length_append, List.length_singleton] at hlen5
    have hlen4 : gs4.length = 4 := by omega
    have hfan4 : ∀ g ∈ gs4, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      fun g hg => hfan' g (List.mem_append_left _ hg)
    have hfan_g4 := hfan' g4 (List.mem_append_right _ List.mem_cons_self)
    rw [notC_append] at hnot
    have hnot4 : notC gs4 ≤ 2 := by omega
    have hmem4 : bHas bT4 ((setMask (foldMasks gs4 [62, 60, 56, 48, 32, 0, 63]) <<< 2) ||| notC gs4) = true := by
      simpa [bTk, hlen4] using foldMasks_in_bTk gs4 (by omega) hfan4 hnot4
    have hc1 := bAll_has hchk hmem4
    set vs4 := foldMasks gs4 [62, 60, 56, 48, 32, 0, 63]
    have ⟨h04, h314, hvs4⟩ := foldMasks_inv gs4 [62, 60, 56, 48, 32, 0, 63] init_inv.1 init_inv.2.1 init_inv.2.2 hfan4
    have hvsF_eq : vsF = vs4 ++ [gateMask vs4 g4] := by simp [vsF, vs4, hgs, foldMasks, List.foldl_append]
    rw [hvsF_eq, setMask_append] at hta_in htb_in htc_in
    have ⟨hm, hc⟩ := pack_shift_or (setMask vs4) (notC gs4) hnot4
    simp only [checkOne, hm, hc] at hc1
    set v := gateMask vs4 g4
    have hv_bit : ∀ x : Nat, ((setMask vs4 ||| (1 <<< v)).testBit x = true) →
        ((setMask vs4).testBit x = true ∨ x = v) := fun x hx => by
      simp only [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at hx
      rcases hx with h | h
      · exact Or.inl h
      · right
        have h1 := (Bool.and_eq_true _ _ |>.mp h).1
        have h2 := (Bool.and_eq_true _ _ |>.mp h).2
        have hvx : v ≤ x := decide_eq_true_eq.mp h1
        cases hd : x - v with
        | zero => omega
        | succ m => rw [hd] at h2; simp [Nat.testBit_succ] at h2
    have hta' := hv_bit ta hta_in; have htb' := hv_bit tb htb_in; have htc' := hv_bit tc htc_in
    have hall : ∃ tgt : Nat, (setMask vs4).testBit tgt = false ∧ tgt = v ∧
        ¬((List.range 64).any fun a =>
          (setMask vs4).testBit a &&
          ((notC gs4 < 2 && ((63 ^^^ a) == tgt)) ||
           (List.range 64).any fun b =>
             (setMask vs4).testBit b && (((a &&& b) == tgt) || ((a ||| b) == tgt)))) = true := by
      have hmiss : ∀ x, ((setMask vs4 ||| (1 <<< v)).testBit x = true) →
          (setMask vs4).testBit x = false → x = v := fun x hx hnf => by
        rcases hv_bit x hx with h | h
        · rw [h] at hnf; exact absurd hnf (by decide)
        · exact h
      cases ba : (setMask vs4).testBit ta
      · have hav : ta = v := hmiss ta hta_in ba
        cases bb : (setMask vs4).testBit tb
        · have hbv : tb = v := hmiss tb htb_in bb
          have hab : tb = ta := hbv.trans hav.symm
          cases bc : (setMask vs4).testBit tc
          · have hcv : tc = v := hmiss tc htc_in bc
            have hac : tc = ta := hcv.trans hav.symm
            refine ⟨ta, ba, hav, ?_⟩
            simpa [ba, bb, bc, hab, hac] using hc1
          · refine ⟨ta, ba, hav, ?_⟩
            simpa [ba, bb, bc, hab] using hc1
        · cases bc : (setMask vs4).testBit tc
          · have hcv : tc = v := hmiss tc htc_in bc
            have hac : tc = ta := hcv.trans hav.symm
            refine ⟨ta, ba, hav, ?_⟩
            simpa [ba, bb, bc, hac] using hc1
          · refine ⟨ta, ba, hav, ?_⟩
            simpa [ba, bb, bc] using hc1
      · cases bb : (setMask vs4).testBit tb
        · have hbv : tb = v := hmiss tb htb_in bb
          cases bc : (setMask vs4).testBit tc
          · have hcv : tc = v := hmiss tc htc_in bc
            have hbc : tc = tb := hcv.trans hbv.symm
            refine ⟨tb, bb, hbv, ?_⟩
            simpa [ba, bb, bc, hbc] using hc1
          · refine ⟨tb, bb, hbv, ?_⟩
            simpa [ba, bb, bc] using hc1
        · cases bc : (setMask vs4).testBit tc
          · refine ⟨tc, bc, hmiss tc htc_in bc, ?_⟩
            simpa [ba, bb, bc] using hc1
          · simp [ba, bb, bc] at hc1
    rcases hall with ⟨tgt, htgt_f, htgt_v, hno⟩
    have hno_b : ((List.range 64).any fun a =>
        (setMask vs4).testBit a &&
        ((notC gs4 < 2 && ((63 ^^^ a) == tgt)) ||
         (List.range 64).any fun b =>
           (setMask vs4).testBit b && (((a &&& b) == tgt) || ((a ||| b) == tgt)))) = false := by
      cases h : ((List.range 64).any fun a =>
        (setMask vs4).testBit a &&
        ((notC gs4 < 2 && ((63 ^^^ a) == tgt)) ||
         (List.range 64).any fun b =>
           (setMask vs4).testBit b && (((a &&& b) == tgt) || ((a ||| b) == tgt))))
      · rfl
      · exact absurd h hno
    rcases hfan_g4 with ⟨hop, _⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have hbit_vs4 : ∀ v' ∈ vs4, (setMask vs4).testBit v' = true := fun _ hv => testBit_setMask_of_mem hv
    have contra_any : ∀ a, a < 64 → (setMask vs4).testBit a = true →
        (notC gs4 < 2 → 63 ^^^ a ≠ tgt) ∧
        ∀ b, b < 64 → (setMask vs4).testBit b = true → a &&& b ≠ tgt ∧ a ||| b ≠ tgt := by
      intro a ha hba
      have hn : ∀ x ∈ List.range 64, ((setMask vs4).testBit x &&
          ((decide (notC gs4 < 2) && ((63 ^^^ x) == tgt)) ||
           (List.range 64).any fun b =>
             (setMask vs4).testBit b && (((x &&& b) == tgt) || ((x ||| b) == tgt)))) = false :=
        fun x hx => Bool.eq_false_iff.mpr (List.any_eq_false.mp hno_b x hx)
      have ha' := hn a (List.mem_range.mpr ha)
      simp only [hba, Bool.true_and, Bool.or_eq_false_iff, Bool.and_eq_false_eq_eq_false_or_eq_false] at ha'
      constructor
      · intro hclt heq
        rcases ha'.1 with hcl | hxq
        · simp [hclt] at hcl
        · simp [heq] at hxq
      · intro b hb hbb
        have hb' := Bool.eq_false_iff.mpr (List.any_eq_false.mp ha'.2 b (List.mem_range.mpr hb))
        simp only [hbb, Bool.true_and, Bool.or_eq_false_iff] at hb'
        constructor <;> intro heq
        · simp [heq] at hb'
        · simp [heq] at hb'
    cases hgop4 : g4.op <;> simp only [hgop4, reduceCtorEq, false_or, or_false] at hop
    · match hi : g4.inputs with
      | [] =>
        have h31t : (setMask vs4).testBit 63 = true := hbit_vs4 63 h314
        have : v = 63 := by simp [v, gateMask, hgop4, hi]
        rw [htgt_v, this] at htgt_f; rw [h31t] at htgt_f; exact Bool.noConfusion htgt_f
      | [a] =>
        have : v = vs4.getD a 0 := by simp [v, gateMask, hgop4, hi]
        rw [htgt_v, this] at htgt_f
        rw [testBit_setMask_getD vs4 h04 a] at htgt_f; exact Bool.noConfusion htgt_f
      | a :: b :: _ =>
        have : v = (vs4.getD a 0) &&& (vs4.getD b 0) := by simp [v, gateMask, hgop4, hi]
        have hc := (contra_any _ (getD_lt_32 vs4 hvs4 a) (testBit_setMask_getD vs4 h04 a)).2 _
          (getD_lt_32 vs4 hvs4 b) (testBit_setMask_getD vs4 h04 b)
        exact hc.1 (this.symm.trans htgt_v.symm)
    · match hi : g4.inputs with
      | [] =>
        have : v = 0 := by simp [v, gateMask, hgop4, hi]
        rw [htgt_v, this] at htgt_f; rw [hbit_vs4 0 h04] at htgt_f; exact Bool.noConfusion htgt_f
      | [a] =>
        have : v = vs4.getD a 0 := by simp [v, gateMask, hgop4, hi]
        rw [htgt_v, this] at htgt_f
        rw [testBit_setMask_getD vs4 h04 a] at htgt_f; exact Bool.noConfusion htgt_f
      | a :: b :: _ =>
        have : v = (vs4.getD a 0) ||| (vs4.getD b 0) := by simp [v, gateMask, hgop4, hi]
        have hc := (contra_any _ (getD_lt_32 vs4 hvs4 a) (testBit_setMask_getD vs4 h04 a)).2 _
          (getD_lt_32 vs4 hvs4 b) (testBit_setMask_getD vs4 h04 b)
        exact hc.2 (this.symm.trans htgt_v.symm)
    · simp only [hgop4, isNotOp, ↓reduceIte] at hnot
      have hclt : notC gs4 < 2 := by omega
      match hi : g4.inputs with
      | [] =>
        have : v = 63 := by simp [v, gateMask, hgop4, hi]
        have h310 : 63 ^^^ 0 = 63 := by decide
        have hc := (contra_any 0 (by decide) (hbit_vs4 0 h04)).1 hclt
        exact hc (h310.trans (this.symm.trans htgt_v.symm))
      | a :: _ =>
        have : v = 63 ^^^ (vs4.getD a 0) := by simp [v, gateMask, hgop4, hi]
        have hc := (contra_any _ (getD_lt_32 vs4 hvs4 a) (testBit_setMask_getD vs4 h04 a)).1 hclt
        exact hc (this.symm.trans htgt_v.symm)

end PEqualNP.Outside.L_meta_50159

theorem PEqualNP.Outside.L_meta_50159 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (28 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val)) := by
  intro ⟨D, p, q, r, hfan, _, hnot, hsize, hm⟩
  exact PEqualNP.Outside.L_meta_50159.no_triple_in_5_gates 28 40 46
    (by decide) (by decide) (by decide) PEqualNP.Outside.L_meta_50159.bAll_target
    D p q r hfan (PEqualNP.Outside.L_meta_50159.notCount_eq_notC D ▸ hnot) hsize hm
