use iced::advanced::layout::{self, Layout};
use iced::advanced::widget::{tree, Tree, Widget};
use iced::advanced::{renderer as adv_renderer, text as adv_text};
use iced::{
    alignment, color, mouse, Element, Length, Pixels, Point, Rectangle, Size, Transformation,
};

const N_COLS: i64 = 50;
const N_ROWS: i64 = 50;
const CELL_BORDER_WIDTH: f32 = 2.0;
const CELL_X_PADDING: f32 = 10.0;
const CELL_Y_PADDING: f32 = 5.0;
const CELL_BASE_HEIGHT: f32 = 30.0;
const CELL_BASE_WIDTH: f32 = 180.0;

#[derive(Debug, Default, Clone, Copy)]
struct State {}

impl State {
    pub fn new() -> Self {
        State::default()
    }
}

pub struct Grid {}

impl Grid {
    pub fn new() -> Self {
        Self {}
    }
}

impl<'a, Message: 'a, Theme, Renderer> From<Grid> for Element<'a, Message, Theme, Renderer>
where
    Renderer: adv_renderer::Renderer + adv_text::Renderer,
{
    fn from(grid: Grid) -> Self {
        Self::new(grid)
    }
}

impl<'a, Message, Theme, Renderer> Widget<Message, Theme, Renderer> for Grid
where
    Renderer: adv_renderer::Renderer + adv_text::Renderer,
{
    fn tag(&self) -> tree::Tag {
        tree::Tag::of::<State>()
    }

    fn state(&self) -> tree::State {
        tree::State::new(State::new())
    }

    fn size(&self) -> Size<Length> {
        Size {
            width: Length::Shrink,
            height: Length::Shrink,
        }
    }

    fn layout(
        &self,
        _tree: &mut Tree,
        _renderer: &Renderer,
        limits: &layout::Limits,
    ) -> layout::Node {
        layout::atomic(limits, Length::Fill, Length::Fill)
    }

    fn draw(
        &self,
        tree: &Tree,
        renderer: &mut Renderer,
        _theme: &Theme,
        _style: &adv_renderer::Style,
        layout: Layout<'_>,
        _cursor: mouse::Cursor,
        viewport: &Rectangle,
    ) {
        let state = tree.state.downcast_ref::<State>();
        let outer_bounds = layout.bounds();
        renderer.with_layer(outer_bounds, |renderer| {
            let transformation = Transformation::translate(outer_bounds.x, outer_bounds.y);
            renderer.with_transformation(transformation, |renderer| {
                self.draw_sheet(renderer, &outer_bounds, state);
            });
        });
    }
}

impl Grid {
    fn draw_sheet<Renderer: adv_renderer::Renderer + adv_text::Renderer>(
        &self,
        renderer: &mut Renderer,
        viewport: &Rectangle,
        state: &State,
    ) {
        for col in 0..=N_COLS {
            for row in 0..=N_ROWS {
                self.draw_cell(col, row, renderer, viewport, state);
            }
        }
    }

    fn get_cell_rect(&self, col: i64, row: i64) -> Rectangle {
        let w = CELL_BASE_WIDTH;
        let h = CELL_BASE_HEIGHT;
        Rectangle {
            x: (col as f32) * w - CELL_BORDER_WIDTH,
            y: (row as f32) * h - CELL_BORDER_WIDTH,
            width: w + 2.0 * CELL_BORDER_WIDTH,
            height: h + 2.0 * CELL_BORDER_WIDTH,
        }
    }

    fn get_cell_inner_rect(&self, cell_rect: Rectangle) -> Rectangle {
        Rectangle {
            x: cell_rect.x + CELL_X_PADDING,
            y: cell_rect.y + CELL_Y_PADDING,
            width: cell_rect.width - (2.0 * CELL_X_PADDING),
            height: cell_rect.height - (2.0 * CELL_Y_PADDING),
        }
    }

    fn draw_cell<Renderer: adv_renderer::Renderer + adv_text::Renderer>(
        &self,
        col: i64,
        row: i64,
        renderer: &mut Renderer,
        bounds: &Rectangle,
        state: &State,
    ) {
        let cell_rect = self.get_cell_rect(col, row);
        let cell_inner_rect = self.get_cell_inner_rect(cell_rect);

        let border = iced::border::rounded(0.0).color(color!(0xf0f0f4)).width(1);

        let background = color!(0xffffff);

        renderer.fill_quad(
            adv_renderer::Quad {
                bounds: cell_rect,
                border,
                ..adv_renderer::Quad::default()
            },
            background,
        );

        let cell_value = "hello";
        let cell_text = adv_text::Text {
            content: cell_value.to_string(),
            font: renderer.default_font(),
            size: Pixels(18.0),
            line_height: adv_text::LineHeight::Relative(1.2),
            bounds: Size::new(f32::INFINITY, bounds.height),
            horizontal_alignment: alignment::Horizontal::Left,
            vertical_alignment: alignment::Vertical::Top,
            shaping: adv_text::Shaping::Basic,
            wrapping: iced::widget::text::Wrapping::Word,
        };

        renderer.fill_text(
            cell_text,
            Point::new(cell_inner_rect.x, cell_inner_rect.y),
            color!(0x111111),
            Rectangle::INFINITE,
        );
    }
}
