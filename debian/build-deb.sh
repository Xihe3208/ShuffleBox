#!/bin/sh
set -eu

SOURCE_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
VERSION=$(sed -n '1s/^shufflebox (\([^)]*\)).*/\1/p' "$SOURCE_DIR/debian/changelog")
PACKAGE_VERSION=${SHUFFLEBOX_PACKAGE_VERSION:-$VERSION}
OUTPUT_DIR=${1:-"$SOURCE_DIR/.."}
OUTPUT_FILE="$OUTPUT_DIR/shufflebox_${PACKAGE_VERSION}_all.deb"
BUILD_DIR=$(mktemp -d "${TMPDIR:-/tmp}/shufflebox-deb.XXXXXX")
PACKAGE_ROOT="$BUILD_DIR/shufflebox"
CONTROL_DIR="$PACKAGE_ROOT/DEBIAN"

cleanup() {
    rm -rf "$BUILD_DIR"
}
trap cleanup EXIT HUP INT TERM

install -d -m 0755 "$PACKAGE_ROOT/opt/ShuffleBox"
cp -a "$SOURCE_DIR/LICENSE" "$SOURCE_DIR/README" "$SOURCE_DIR/package.json" \
    "$SOURCE_DIR/server.js" "$SOURCE_DIR/bin" "$SOURCE_DIR/en" "$SOURCE_DIR/zh" \
    "$PACKAGE_ROOT/opt/ShuffleBox/"

install -d -m 0755 "$PACKAGE_ROOT/usr/bin"
install -m 0755 "$SOURCE_DIR/bin/shufflebox" "$PACKAGE_ROOT/usr/bin/shufflebox"
install -d -m 0755 "$PACKAGE_ROOT/usr/share/shufflebox"
install -m 0640 "$SOURCE_DIR/debian/shufflebox.env" \
    "$PACKAGE_ROOT/usr/share/shufflebox/shufflebox.env.example"
install -d -m 0755 "$PACKAGE_ROOT/lib/systemd/system"
install -m 0644 "$SOURCE_DIR/debian/shufflebox.service" \
    "$PACKAGE_ROOT/lib/systemd/system/shufflebox.service"
install -d -m 0755 "$PACKAGE_ROOT/usr/share/doc/shufflebox"
install -m 0644 "$SOURCE_DIR/debian/copyright" \
    "$PACKAGE_ROOT/usr/share/doc/shufflebox/copyright"

install -d -m 0755 "$CONTROL_DIR"
sed "s/^Version: .*/Version: $PACKAGE_VERSION/" \
    "$SOURCE_DIR/debian/control.binary" > "$CONTROL_DIR/control"
install -m 0755 "$SOURCE_DIR/debian/shufflebox.preinst" "$CONTROL_DIR/preinst"
install -m 0755 "$SOURCE_DIR/debian/shufflebox.postinst" "$CONTROL_DIR/postinst"
install -m 0755 "$SOURCE_DIR/debian/shufflebox.prerm" "$CONTROL_DIR/prerm"
install -m 0755 "$SOURCE_DIR/debian/shufflebox.postrm" "$CONTROL_DIR/postrm"

find "$PACKAGE_ROOT" -type f ! -path "$CONTROL_DIR/*" -printf '%P\n' \
    | sort \
    | while IFS= read -r file; do
        md5sum "$PACKAGE_ROOT/$file"
    done \
    | sed "s#  $PACKAGE_ROOT/#  #" > "$CONTROL_DIR/md5sums"

mkdir -p "$OUTPUT_DIR"
dpkg-deb --build --root-owner-group "$PACKAGE_ROOT" "$OUTPUT_FILE"
printf '%s\n' "$OUTPUT_FILE"
