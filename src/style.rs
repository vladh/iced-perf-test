// © 2022 Vlad-Stefan Harbuz <vlad@vladh.net>
// SPDX-License-Identifier: AGPL-3.0-only
// “Cellsum” is a registered trademark and no rights to it are ceded.

//! Provides styling information such as colours for drawing.

use iced::advanced::text as adv_text;
use iced::widget::canvas;
use iced::{color, Pixels};
use once_cell::sync::Lazy;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Transparent,
    Bg,
    Text,
    Primary,
    Success,
    Danger,
    CellNormal,
    CellHeader,
    CellHovered,
    CellSelected,
    CellNormalBorder,
    CellHeaderBorder,
    CellHoveredBorder,
    CellSelectedInnerBorder,
    CellSelectedOuterBorder,
}

impl From<Color> for iced::Color {
    fn from(value: Color) -> Self {
        match value {
            Color::Transparent => color!(0xffffff, 0.0),
            Color::Bg => color!(0xf6f6fc),
            Color::Text => color!(0x111111),
            Color::Primary => color!(0x0055ee),
            Color::Success => color!(0x00aa00),
            Color::Danger => color!(0xaa0000),
            Color::CellNormal => color!(0xffffff),
            Color::CellHeader => color!(0xf0f0f4),
            Color::CellHovered => color!(0xf6f6f6),
            Color::CellSelected => color!(0xf0f0ff),
            Color::CellNormalBorder => color!(0xf0f0f4),
            Color::CellHeaderBorder => color!(0xe6e6ec),
            Color::CellHoveredBorder => color!(0x0055ee),
            Color::CellSelectedInnerBorder => color!(0xd0d6f0, 0.5),
            Color::CellSelectedOuterBorder => color!(0x0055ee),
        }
    }
}

impl From<Color> for canvas::Fill {
    fn from(value: Color) -> canvas::Fill {
        iced::Color::from(value).into()
    }
}

impl From<Color> for iced::Background {
    fn from(value: Color) -> iced::Background {
        iced::Background::Color(iced::Color::from(value))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Stroke {
    CellNormal,
}

impl From<Stroke> for canvas::Stroke<'_> {
    fn from(value: Stroke) -> Self {
        match value {
            Stroke::CellNormal => canvas::Stroke {
                style: canvas::stroke::Style::Solid(iced::Color::BLACK),
                width: 2.0,
                ..canvas::Stroke::default()
            },
        }
    }
}

#[derive(Debug)]
pub struct FontProps {
    pub shaping: adv_text::Shaping,
    pub size: Pixels,
    pub line_height: adv_text::LineHeight,
}

pub static FONT_PROPS: Lazy<FontProps> = Lazy::new(|| FontProps {
    shaping: adv_text::Shaping::Basic,
    size: Pixels(18.0),
    line_height: adv_text::LineHeight::Relative(1.2),
});
