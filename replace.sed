# Lambda and right arrow.
s/\\textbackslash/\$\\lambda\$/g
s/->/\$\\to\$/g

# Equality.
s/==/\$\\equiv\$/g

# Append.
s/++/\$+\\!+\$/g

# Comments.
s/AgdaComment{\-\-/AgdaComment\{\-\-\-/g

# Bind and then.
s/>>=/\$\\mathbin\{>\\!\\!\\!>\\mkern-6.7mu=\}\$/g
s/>>/\$\\mathbin\{>\\!\\!\\!>}\$/g

# Unit.
s/<>/\$\\langle\\rangle\$/g
