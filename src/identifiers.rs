//! Descriptions of well-known databases of format specifications.
//! Each type in this module can validate it's content to point out
//! KSY writers to possible mistakes in theirs KSY files.

use serde::Deserialize;

/// Name of page in [MediaWiki].
///
/// Hand-crafted regex, it should match any valid URL path.
///
/// Pattern: `^([a-zA-Z0-9$\-._~+!*'(),@&;:/]+|%[0-9a-fA-F]{2})+$`.
///
/// [MediaWiki]: https://www.mediawiki.org/wiki/MediaWiki
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct MediaWiki(String);

/// [ISO standard][iso] identifier.
///
/// [Pattern]: `^[1-9]\d*([-–][0-9]+)?(:(19|20)\d{2})?$`.
///
/// [iso]: https://www.iso.org/
/// [Pattern]: https://www.wikidata.org/wiki/Property:P503#P1793
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct Iso(String);

/// [Library of Congress][loc] Format Description Document ID.
///
/// [Pattern]: `^fdd\d{6}$`.
///
/// [loc]: https://www.loc.gov/
/// [Pattern]: https://www.wikidata.org/wiki/Property:P3266#P1793
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct Loc(String);

/// [IANA media type][mime].
///
/// This regex pattern is hand-crafted and not coming from any specification,
/// but it's tested against all registered discrete IANA media types (multipart
/// types don't make sense for Kaitai Struct).
///
/// Pattern: `^(application|audio|font|image|model|text|video)/([a-zA-Z0-9]+[.\-_+]?)*[a-zA-Z0-9]$`.
///
/// [mime]: https://www.iana.org/assignments/media-types/media-types.xhtml
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct MimeType(String);

/// Identifier (PUID) for a file format in the technical registry [PRONOM]
///
/// [Pattern]: `^(x-)?fmt/\d+$`.
///
/// [PRONOM]: https://www.nationalarchives.gov.uk/PRONOM/Default.aspx
/// [Pattern]: https://www.wikidata.org/wiki/Property:P2748#P1793
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct Pronom(String);

/// Identifier for an item in [Request for Comments][rfc], a publication of IETF
/// and the Internet Society.
///
/// [rfc]: https://en.wikipedia.org/wiki/Request_for_Comments
#[derive(Clone, Debug, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum Rfc {
  /// RFC ID, specified, as number
  Number(usize),
  /// RFC ID, specified, as string (without "RFC" prefix).
  ///
  /// [Pattern]: `^[1-9]\d*$`.
  ///
  /// [Pattern]: https://www.wikidata.org/wiki/Property:P892#P1793
  String(String),
}

/// Unique identifier (UID) used in [Wikidata].
///
/// [Pattern]: `^Q[1-9]\d*$`.
///
/// [Wikidata]: https://www.wikidata.org/
/// [Pattern]: https://www.wikidata.org/wiki/Q43649390#P1793
#[derive(Clone, Debug, Default, Deserialize, PartialEq)]
#[serde(transparent)]
pub struct Wikidata(String);
