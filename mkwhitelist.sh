(echo -ne 'module Whitelist(allowed) where\n\nallowed :: String -> Bool\nallowed = (`elem`[\n' ; (find doc -type f; find static -type f) | awk 'length(a)!=0 {printf a"\",\n"; a = "  \""$1} length(a)==0 {a = "  \""$1} END {printf a"\"])\n"}') > App/Whitelist.hs
