#!/bin/bash - 

file=${1}

if [[ ! -s ${file} ]]; then
  echo "$0 <file>" >> /dev/stderr
  exit 1
fi

filename=$(basename $file)
dirname=$(dirname $file)

aapt dump badging ${file} > /dev/null 2>&1 || exit 1

prefix=$(aapt dump badging ${file} | perl -wnle "print \"\$1-\$2\" if /^package:\s+name='([^']+)'\s+versionCode='([^']+)'/")
sha256=$(sha256sum ${file} | awk '{print $1}')

newname="${prefix}-${sha256}.apk"

if [[ -n "$prefix" && -n "$newname" ]]; then
  rename "$filename" "$newname" "$file"
fi
